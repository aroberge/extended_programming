from __future__ import annotations

import argparse
import ast
import fnmatch
import html
import json
import re
import sys
import tempfile
import webbrowser
from datetime import datetime
from pathlib import Path, PurePosixPath

from epy.node import Node

SKIP_DIRS = {
    "venv",
    ".venv",
    "env",
    "__pycache__",
    "node_modules",
    "site-packages",
    "build",
    "dist",
    ".git",
    ".mypy_cache",
    ".pytest_cache",
    ".tox",
}
FUNC = ("def", "method")
DEFS = ("def", "method", "class")
MAX_DEPTH = 6


def first_line(s: str | None) -> str:
    if not s:
        return ""
    line = s.strip().splitlines()[0].strip()
    return line if len(line) <= 100 else line[:99] + "…"


def dotted(expr) -> str | None:
    parts = []
    while isinstance(expr, ast.Attribute):
        parts.append(expr.attr)
        expr = expr.value
    if isinstance(expr, ast.Name):
        parts.append(expr.id)
        return ".".join(reversed(parts))
    return None


def unparse(node) -> str:
    try:
        return ast.unparse(node)
    except Exception:
        return "…"


def start_of(st) -> int:
    decos = getattr(st, "decorator_list", None) or []
    return min([d.lineno for d in decos] + [st.lineno])


def is_main_guard(st) -> bool:
    if not isinstance(st, ast.If) or not isinstance(st.test, ast.Compare):
        return False
    t = st.test
    sides = [t.left, *t.comparators]
    return any(isinstance(s, ast.Name) and s.id == "__name__" for s in sides) and any(
        isinstance(s, ast.Constant) and s.value == "__main__" for s in sides
    )


def category(st, in_class: bool) -> str:
    if isinstance(st, ast.ClassDef):
        return "class"
    if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return "def"
    if isinstance(st, (ast.Import, ast.ImportFrom)):
        return "imports"
    if is_main_guard(st):
        return "main"
    if isinstance(st, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        return "attrs" if in_class else "globals"
    if (
        isinstance(st, ast.Expr)
        and isinstance(st.value, ast.Constant)
        and isinstance(st.value.value, str)
    ):
        return "doc"
    return "script"


def direct_defs(body):
    for st in body:
        if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            yield st
            continue
        for name in ("body", "orelse", "finalbody", "handlers", "cases"):
            sub = getattr(st, name, None)
            if isinstance(sub, list):
                yield from direct_defs(sub)


def scan_scope(stmts):
    calls, refs, types = [], [], {}
    stack = list(stmts)
    while stack:
        n = stack.pop()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        if isinstance(n, ast.Call):
            d = dotted(n.func)
            if d:
                calls.append((n.lineno, n.col_offset, d))
            for a in [*n.args, *(k.value for k in n.keywords)]:
                if isinstance(a, (ast.Name, ast.Attribute)) and (d2 := dotted(a)):
                    refs.append((a.lineno, a.col_offset, d2))
        elif isinstance(n, (ast.Assign, ast.AnnAssign)) and isinstance(
            n.value, ast.Call
        ):
            d = dotted(n.value.func)
            targets = n.targets if isinstance(n, ast.Assign) else [n.target]
            for t in targets:
                if d and (td := dotted(t)):
                    types[td] = d
        stack.extend(ast.iter_child_nodes(n))
    order = lambda xs: list(dict.fromkeys(r for _, _, r in sorted(xs)))
    return order(calls), order(refs), types


def block_preview(kind: str, stmts) -> str:
    names = []
    for st in stmts:
        if isinstance(st, ast.Import):
            names += [a.asname or a.name for a in st.names]
        elif isinstance(st, ast.ImportFrom):
            names.append(("." * st.level) + (st.module or ""))
        elif isinstance(st, ast.Assign):
            names += [unparse(t) for t in st.targets]
        elif isinstance(st, (ast.AnnAssign, ast.AugAssign)):
            names.append(unparse(st.target))
    names = list(dict.fromkeys(names))
    if not names:
        if kind != "script":
            return ""
        first = unparse(stmts[0]).splitlines()[0]
        return (first if len(first) <= 50 else first[:49] + "…") + (
            " …" if len(stmts) > 1 else ""
        )
    s = ", ".join(names[:6]) + (f", +{len(names) - 6}" if len(names) > 6 else "")
    return s if len(s) <= 70 else s[:69] + "…"


class FileGraph:
    def __init__(self, rel: str, src: str):
        self.rel = rel
        self.lines = src.splitlines()
        self.imports: dict[str, tuple[str, str | None, int]] = {}
        self.star: list[tuple[str, int]] = []
        self.dep_specs: list[tuple[str, str | None, int]] = []
        self.ids: set[str] = set()
        self.root = Node(
            id=rel,
            kind="module",
            name=PurePosixPath(rel).name,
            qual="",
            file=rel,
            start=1,
            end=max(1, len(self.lines)),
        )
        try:
            tree = ast.parse(src, filename=rel)
        except SyntaxError as e:
            self.root.error = f"SyntaxError line {e.lineno}: {e.msg}"
            return
        self.root.doc = first_line(ast.get_docstring(tree))
        self._imports(tree)
        self.root.children = self._segment(
            tree.body, self.root, in_class=False, prev_end=0
        )

    def _imports(self, tree):
        for n in ast.walk(tree):
            if isinstance(n, ast.Import):
                for a in n.names:
                    self.dep_specs.append((a.name, None, 0))
                    if a.asname:
                        self.imports[a.asname] = (a.name, None, 0)
                    else:
                        top = a.name.split(".")[0]
                        self.imports[top] = (top, None, 0)
            elif isinstance(n, ast.ImportFrom):
                mod = n.module or ""
                for a in n.names:
                    self.dep_specs.append(
                        (mod, a.name if a.name != "*" else None, n.level)
                    )
                    if a.name == "*":
                        self.star.append((mod, n.level))
                    else:
                        self.imports[a.asname or a.name] = (mod, a.name, n.level)

    def _lead(self, start: int, prev_end: int) -> int:
        while start - 1 > prev_end and self.lines[start - 2].lstrip().startswith("#"):
            start -= 1
        return start

    def _mk(self, kind, name, parent, s, e, qual) -> Node:
        base = f"{self.rel}::{qual}"
        nid, i = base, 2
        while nid in self.ids:
            nid, i = f"{base}#{i}", i + 1
        self.ids.add(nid)
        return Node(
            id=nid,
            kind=kind,
            name=name,
            qual=qual,
            file=self.rel,
            start=s,
            end=e,
            parent=parent,
        )

    def _scan(self, n: Node, stmts):
        n.raw_calls, n.raw_refs, n.types = scan_scope(stmts)

    def _segment(self, body, parent: Node, in_class: bool, prev_end: int) -> list[Node]:
        out: list[Node] = []
        group: list = []
        gkind = None

        def flush():
            nonlocal group, gkind, prev_end
            if group:
                if gkind == "code":
                    gkind = (
                        "script"
                        if any(category(g, in_class) == "script" for g in group)
                        else ("attrs" if in_class else "globals")
                    )
                s = self._lead(start_of(group[0]), prev_end)
                e = group[-1].end_lineno
                q = f"{parent.qual}.<{gkind}@{s}>" if parent.qual else f"<{gkind}@{s}>"
                n = self._mk(gkind, gkind, parent, s, e, q)
                n.sig = block_preview(gkind, group)
                if gkind == "doc":
                    n.doc = first_line(group[0].value.value)
                self._scan(n, group)
                if parent.kind == "module":
                    parent.types.update(n.types)
                out.append(n)
                prev_end = e
            group, gkind = [], None

        for st in body:
            k = category(st, in_class)
            if k in ("globals", "attrs", "script"):
                k = "code"
            if k in ("class", "def"):
                flush()
                n = self._def(st, parent, in_class, prev_end)
                out.append(n)
                prev_end = n.end
            else:
                if k != gkind:
                    flush()
                    gkind = k
                group.append(st)
        flush()
        return out

    def _def(self, st, parent: Node, in_class: bool, prev_end: int) -> Node:
        s = self._lead(start_of(st), prev_end)
        qual = f"{parent.qual}.{st.name}" if parent.qual else st.name
        if isinstance(st, ast.ClassDef):
            n = self._mk("class", st.name, parent, s, st.end_lineno, qual)
            n.bases = [dotted(b) or unparse(b) for b in st.bases]
            n.sig = f"({', '.join(unparse(b) for b in st.bases)})" if st.bases else ""
            n.children = self._segment(st.body, n, in_class=True, prev_end=st.lineno)
        else:
            n = self._mk(
                "method" if in_class else "def", st.name, parent, s, st.end_lineno, qual
            )
            n.is_async = isinstance(st, ast.AsyncFunctionDef)
            ret = f" -> {unparse(st.returns)}" if st.returns else ""
            n.sig = f"({unparse(st.args)}){ret}"
            n.children = [
                self._def(d, n, False, st.lineno) for d in direct_defs(st.body)
            ]
            self._scan(n, st.body)
            if in_class:
                for k, v in n.types.items():
                    if k.startswith(("self.", "cls.")):
                        parent.types.setdefault(k, v)
        n.doc = first_line(ast.get_docstring(st))
        n.decorators = [unparse(d) for d in st.decorator_list]
        return n


def iter_py(root: Path, excludes: list[str]):
    if root.is_file():
        yield root
        return
    for p in sorted(root.rglob("*.py")):
        rel = p.relative_to(root)
        if any(part in SKIP_DIRS or part.startswith(".") for part in rel.parts[:-1]):
            continue
        if any(fnmatch.fnmatch(rel.as_posix(), pat) for pat in excludes):
            continue
        yield p


class Project:
    def __init__(self, path: Path, excludes: list[str] | None = None):
        path = path.resolve()
        self.root = path.parent if path.is_file() else path
        self.files: dict[str, FileGraph] = {}
        for p in iter_py(path, excludes or []):
            rel = p.relative_to(self.root).as_posix()
            self.files[rel] = FileGraph(
                rel, p.read_text(encoding="utf-8", errors="replace")
            )
        self.nodes: dict[str, Node] = {
            n.id: n for fg in self.files.values() for n in fg.root.walk()
        }
        self.modindex: dict[str, list[str]] = {}
        for rel in self.files:
            parts = rel[:-3].split("/")
            if parts[-1] == "__init__":
                parts = parts[:-1]
            for i in range(len(parts)):
                self.modindex.setdefault(".".join(parts[i:]), []).append(rel)
        self.deps: dict[str, list[str]] = {}
        self.rdeps: dict[str, list[str]] = {rel: [] for rel in self.files}
        self._link()

    def resolve_module(self, mod: str, from_rel: str, level: int) -> str | None:
        if level:
            base = PurePosixPath(from_rel).parent
            for _ in range(level - 1):
                base = base.parent
            cand = base / mod.replace(".", "/") if mod else base
            for c in (f"{cand}.py", f"{cand}/__init__.py"):
                c = str(PurePosixPath(c))
                if c in self.files:
                    return c
            return None
        cands = self.modindex.get(mod)
        if not cands:
            return None
        here = PurePosixPath(from_rel).parent.parts

        def score(c):
            there = PurePosixPath(c).parent.parts
            common = 0
            for a, b in zip(here, there):
                if a != b:
                    break
                common += 1
            return (there != here, -common, len(c))

        return min(cands, key=score)

    def import_target(self, mod, attr, level, from_rel, depth) -> Node | None:
        if depth > MAX_DEPTH:
            return None
        rel = self.resolve_module(mod, from_rel, level)
        if attr is None:
            return self.files[rel].root if rel else None
        if rel and (hit := self.member(self.files[rel].root, attr, depth + 1)):
            return hit
        sub = self.resolve_module(f"{mod}.{attr}" if mod else attr, from_rel, level)
        return self.files[sub].root if sub else None

    def member(self, node: Node, name: str, depth: int) -> Node | None:
        if depth > MAX_DEPTH or node is None:
            return None
        hits = [c for c in node.children if c.kind in DEFS and c.name == name]
        if hits:
            return hits[-1]
        if node.kind == "module":
            fg = self.files[node.file]
            if name in fg.imports:
                return self.import_target(*fg.imports[name], node.file, depth + 1)
            if node.file.endswith("__init__.py"):
                sub = self.resolve_module(name, node.file, 1)
                return self.files[sub].root if sub else None
        elif node.kind == "class":
            for b in node.bases:
                bt = self.resolve(b, node.parent, depth + 1)
                if bt is not None and bt.kind == "class" and bt is not node:
                    if hit := self.member(bt, name, depth + 1):
                        return hit
        return None

    def descend(self, node: Node | None, parts: list[str], depth: int) -> Node | None:
        for p in parts:
            if node is None:
                return None
            node = self.member(node, p, depth)
        return node

    def lookup(self, name: str, scope: Node, depth: int) -> Node | None:
        s = scope
        while s is not None:
            if s.kind in FUNC or s.kind == "module":
                hits = [c for c in s.children if c.kind in DEFS and c.name == name]
                if hits:
                    return hits[-1]
            if s.kind == "module":
                break
            s = s.parent
        fg = self.files[scope.file]
        if name in fg.imports:
            return self.import_target(*fg.imports[name], scope.file, depth + 1)
        for mod, level in fg.star:
            rel = self.resolve_module(mod, scope.file, level)
            if rel and (hit := self.member(self.files[rel].root, name, depth + 1)):
                return hit
        return None

    @staticmethod
    def type_of(key: str, scope: Node) -> str | None:
        s = scope
        while s is not None:
            if key in s.types:
                return s.types[key]
            s = s.parent
        return None

    @staticmethod
    def enclosing_class(scope: Node) -> Node | None:
        s = scope
        while s is not None and s.kind != "class":
            s = s.parent
        return s

    def resolve(self, raw: str, scope: Node, depth: int = 0) -> Node | None:
        if depth > MAX_DEPTH or scope is None:
            return None
        parts = raw.split(".")
        for k in range(len(parts) - 1, 0, -1):
            t = self.type_of(".".join(parts[:k]), scope)
            if t:
                cls = self.resolve(t, scope, depth + 1)
                if cls is not None and cls.kind == "class":
                    return self.descend(cls, parts[k:], depth + 1)
                break
        if parts[0] in ("self", "cls"):
            cls = self.enclosing_class(scope)
            return (
                self.descend(cls, parts[1:], depth + 1)
                if cls and len(parts) > 1
                else None
            )
        hit = self.lookup(parts[0], scope, depth + 1)
        return self.descend(hit, parts[1:], depth + 1) if hit else None

    def _link(self):
        for n in self.nodes.values():
            out = []
            for raw in n.raw_calls:
                t = self.resolve(raw, n)
                if t is not None and t.kind in DEFS:
                    out.append(t.id)
                else:
                    n.external.append(raw)
            for raw in n.raw_refs:
                t = self.resolve(raw, n)
                if t is not None and t.kind in DEFS:
                    out.append(t.id)
            n.calls = list(dict.fromkeys(out))
        for n in self.nodes.values():
            for t in n.calls:
                self.nodes[t].callers.append(n.id)
        for rel, fg in self.files.items():
            ds = []
            for mod, attr, level in fg.dep_specs:
                r = (
                    self.resolve_module(
                        f"{mod}.{attr}" if attr and mod else (attr or mod), rel, level
                    )
                    if attr
                    else None
                )
                r = r or self.resolve_module(mod, rel, level)
                if r and r != rel:
                    ds.append(r)
            self.deps[rel] = sorted(set(ds))
            for d in self.deps[rel]:
                self.rdeps[d].append(rel)

    def find(self, target: str) -> list[Node]:
        def match_files(f):
            f = f.removeprefix("./")
            return (
                [f]
                if f in self.files
                else [r for r in self.files if r.endswith("/" + f)]
            )

        m = re.fullmatch(r"(.+\.py):(\d+)", target)
        if m or ("::" in target and target.split("::", 1)[1].isdigit()):
            f, line = (
                (m.group(1), int(m.group(2)))
                if m
                else (target.split("::")[0], int(target.split("::")[1]))
            )
            out = []
            for rel in match_files(f):
                best = self.files[rel].root
                while True:
                    inner = [c for c in best.children if c.start <= line <= c.end]
                    if not inner:
                        break
                    best = inner[0]
                out.append(best)
            return out
        if "::" in target:
            f, q = target.split("::", 1)
            rels = set(match_files(f))
            return [
                n
                for n in self.nodes.values()
                if n.file in rels and (n.qual == q or n.id.endswith("::" + q))
            ]
        if target.endswith(".py"):
            return [self.files[r].root for r in match_files(target)]
        exact = [n for n in self.nodes.values() if n.qual == target]
        return exact or [
            n
            for n in self.nodes.values()
            if n.kind in DEFS and (n.qual.endswith("." + target) or n.name == target)
        ]

    def stats(self) -> dict:
        ns = self.nodes.values()
        return {
            "files": len(self.files),
            "lines": sum(fg.root.end for fg in self.files.values()),
            "classes": sum(n.kind == "class" for n in ns),
            "functions": sum(n.kind in FUNC for n in ns),
            "edges": sum(len(n.calls) for n in ns),
            "errors": sum(bool(fg.root.error) for fg in self.files.values()),
        }

    def to_dict(self, with_source: bool) -> dict:
        def nd(n: Node) -> dict:
            d = {
                "id": n.id,
                "k": n.kind,
                "n": n.name,
                "q": n.qual,
                "s": n.start,
                "e": n.end,
            }
            for key, val in (
                ("sig", n.sig),
                ("doc", n.doc),
                ("dec", n.decorators),
                ("a", n.is_async),
                ("c", n.calls),
                ("b", n.callers),
                ("x", n.external[:12]),
                ("err", n.error),
                ("ch", [nd(c) for c in n.children]),
            ):
                if val:
                    d[key] = val
            return d

        data = {
            "root": str(self.root),
            "generated": datetime.now().isoformat(timespec="seconds"),
            "stats": self.stats(),
            "files": [
                {
                    "path": rel,
                    "deps": self.deps[rel],
                    "rdeps": sorted(self.rdeps[rel]),
                    "root": nd(fg.root),
                }
                for rel, fg in sorted(self.files.items())
            ],
        }
        if with_source:
            data["src"] = {rel: "\n".join(fg.lines) for rel, fg in self.files.items()}
        return data


def short_sig(n: Node, width: int = 46) -> str:
    sig = n.sig
    if n.kind == "method":
        sig = re.sub(r"^\((self|cls)(, )?", "(", sig)
    return sig if len(sig) <= width else sig[: width - 2] + "…)"


def label(n: Node) -> str:
    if n.kind == "class":
        return f"class {n.name}{short_sig(n)}"
    if n.kind in FUNC:
        deco = "@" + n.decorators[0].split("(")[0] + " " if n.decorators else ""
        return f"{deco}{'async ' if n.is_async else ''}def {n.name}{short_sig(n)}"
    if n.kind == "main":
        return "main  if __name__ == '__main__'"
    if n.kind == "doc":
        return f'doc   "{n.doc[:40]}"' if n.doc else "doc"
    return f"{n.kind:<7} {n.sig}" if n.sig else n.kind


def ref_name(proj: Project, tid: str, src: Node) -> str:
    t = proj.nodes[tid]
    if t.file != src.file:
        return f"{PurePosixPath(t.file).stem}:{t.qual}"
    cls = Project.enclosing_class(src)
    if cls is not None and t.parent is cls:
        return t.name
    return t.qual


def render_map(
    proj: Project, depth: int = 99, calls: bool = True, external: bool = False
) -> str:
    st = proj.stats()
    out = [
        f"# epy · extended python graph · {proj.root}",
        f"# {st['files']} files · {st['lines']:,} lines · {st['classes']} classes · "
        f"{st['functions']} functions · {st['edges']} call edges",
        "# [a-b] line span · NL lines · ←n called from n boxes · → resolved calls"
        + (" · ⋯ external calls" if external else ""),
        "# pull code for any box:  epy.py show <path> <file.py::Qual.name | file.py:LINE>",
        "",
    ]
    for rel in sorted(proj.files):
        fg = proj.files[rel]
        m = fg.root
        out.append(f"@ {rel}  [1-{m.end}] {m.end}L" + (f'  "{m.doc}"' if m.doc else ""))
        if m.error:
            out.append(f"  !! {m.error}")
        if proj.deps[rel]:
            out.append("  ⇢ uses     " + ", ".join(proj.deps[rel]))
        if proj.rdeps[rel]:
            out.append("  ⇠ used by  " + ", ".join(sorted(proj.rdeps[rel])))

        rows: list[tuple[str, Node]] = []

        def walk(nodes, prefix, level):
            for i, n in enumerate(nodes):
                last = i == len(nodes) - 1
                rows.append((prefix + ("└ " if last else "├ ") + label(n), n))
                if n.children and level < depth:
                    walk(n.children, prefix + ("  " if last else "│ "), level + 1)

        walk(m.children, "  ", 1)

        w = min(64, max((len(r) for r, _ in rows), default=0))
        for text, n in rows:
            if len(text) > w:
                text = text[: w - 1] + "…"
            line = f"{text:<{w}}  [{n.start}-{n.end}]".ljust(w + 14) + f"{n.lines:>4}L"
            extra = []
            if n.callers:
                extra.append(f"←{len(n.callers)}")
            if calls and n.calls:
                names = [ref_name(proj, t, n) for t in n.calls]
                extra.append(
                    "→ "
                    + ", ".join(names[:6])
                    + (f" +{len(names) - 6}" if len(names) > 6 else "")
                )
            if external and n.external:
                extra.append(
                    "⋯ "
                    + ", ".join(n.external[:5])
                    + (" …" if len(n.external) > 5 else "")
                )
            out.append(line + ("  " + "  ".join(extra) if extra else ""))
        out.append("")
    return "\n".join(out)


def render_show(proj: Project, n: Node) -> str:
    fg = proj.files[n.file]
    kw = {"def": "def", "method": "def", "class": "class"}.get(n.kind, n.kind)
    head = [f"# {n.file}::{n.qual or '<module>'}  {kw}  [{n.start}-{n.end}] {n.lines}L"]
    if n.sig:
        head.append(f"# sig: {n.sig}")
    if n.children:
        head.append(
            "# boxes: "
            + ", ".join(f"{c.name}[{c.start}-{c.end}]" for c in n.children[:20])
        )
    if n.calls:
        head.append("# calls: " + ", ".join(ref_name(proj, t, n) for t in n.calls))
    if n.callers:
        head.append(
            "# called by: " + ", ".join(ref_name(proj, t, n) for t in n.callers)
        )
    w = len(str(n.end))
    body = [
        f"{i:>{w}} | {fg.lines[i - 1]}"
        for i in range(n.start, min(n.end, len(fg.lines)) + 1)
    ]
    return "\n".join(head + body)


def render_html(
    proj: Project, with_source: bool = True, start: str | None = None
) -> str:
    data = proj.to_dict(with_source)
    data["start"] = start
    blob = json.dumps(data, separators=(",", ":")).replace("<", "\\u003c")
    filepath = Path(__file__)
    directory = filepath.parent
    with open(directory / "template.html", "r") as f:
        html_template = f.read()
    return html_template.replace("__EPY_TITLE__", html.escape(proj.root.name)).replace(
        "__EPY_DATA__", blob
    )


def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="epy", description="extended python graph — block map of a Python codebase"
    )
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("path", type=Path, help="a .py file or a directory")
        p.add_argument(
            "--exclude",
            action="append",
            default=[],
            metavar="GLOB",
            help="skip files matching this glob (relative path), repeatable",
        )
        return p

    m = common(sub.add_parser("map", help="print the block map (.epy text)"))
    m.add_argument("-o", "--out", type=Path)
    m.add_argument("--depth", type=int, default=99, help="nesting depth to print")
    m.add_argument("--no-calls", action="store_true", help="hide → call lists")
    m.add_argument(
        "--external", action="store_true", help="also list unresolved external calls"
    )

    s = common(
        sub.add_parser("show", help="print one box's code with its calls/callers")
    )
    s.add_argument(
        "target", help="file.py::Class.method | Class.method | file.py:LINE | file.py"
    )

    h = common(sub.add_parser("html", help="write the interactive flowchart"))
    h.add_argument("-o", "--out", type=Path, default=Path("epy.html"))
    h.add_argument("--no-source", action="store_true", help="don't embed source code")

    v = common(
        sub.add_parser("view", help="build the mind map and open it in the browser")
    )
    v.add_argument(
        "--root",
        type=Path,
        help="project root for cross-file links (default: cwd if PATH is inside it)",
    )
    v.add_argument(
        "-o", "--out", type=Path, help="where to write the html (default: temp dir)"
    )

    j = common(sub.add_parser("json", help="write the raw graph as JSON"))
    j.add_argument("-o", "--out", type=Path, default=Path("epy.json"))
    j.add_argument("--no-source", action="store_true")

    a = ap.parse_args(argv)
    if not a.path.exists():
        ap.error(f"{a.path} does not exist")
    if a.cmd == "view":
        target = a.path.resolve()
        if a.root:
            root = a.root.resolve()
        elif target.is_file():
            root = Path.cwd() if Path.cwd() in target.parents else target.parent
        else:
            root = target
        proj = Project(root, a.exclude)
        start = target.relative_to(root).as_posix() if target.is_file() else None
        out = a.out or Path(tempfile.gettempdir()) / "epy" / f"{root.name}.html"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(render_html(proj, True, start), encoding="utf-8")
        print(f"wrote {out}")
        webbrowser.open(out.resolve().as_uri())
        return
    proj = Project(a.path, a.exclude)

    if a.cmd == "map":
        text = render_map(proj, a.depth, not a.no_calls, a.external)
        if a.out:
            a.out.write_text(text + "\n", encoding="utf-8")
            print(
                f"wrote {a.out}  ({len(text.splitlines())} lines, {len(text):,} chars)"
            )
        else:
            print(text)
    elif a.cmd == "show":
        hits = proj.find(a.target)
        if not hits:
            sys.exit(f"no box matches {a.target!r}")
        if len(hits) > 1:
            print(
                f"{len(hits)} boxes match {a.target!r}; be more specific:",
                file=sys.stderr,
            )
            for n in hits[:40]:
                print(f"  {n.file}::{n.qual}  [{n.start}-{n.end}]", file=sys.stderr)
            sys.exit(1)
        print(render_show(proj, hits[0]))
    elif a.cmd == "html":
        a.out.write_text(render_html(proj, not a.no_source), encoding="utf-8")
        st = proj.stats()
        print(
            f"wrote {a.out}  ({st['files']} files, {st['lines']:,} lines, {st['edges']} edges)"
        )
    elif a.cmd == "json":
        a.out.write_text(
            json.dumps(proj.to_dict(not a.no_source), indent=1), encoding="utf-8"
        )
        print(f"wrote {a.out}")


if __name__ == "__main__":
    main()
