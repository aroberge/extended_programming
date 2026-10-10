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
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path, PurePosixPath

SKIP_DIRS = {"venv", ".venv", "env", "__pycache__", "node_modules", "site-packages",
             "build", "dist", ".git", ".mypy_cache", ".pytest_cache", ".tox"}
FUNC = ("def", "method")
DEFS = ("def", "method", "class")
MAX_DEPTH = 6


@dataclass(eq=False)
class Node:
    id: str
    kind: str
    name: str
    qual: str
    file: str
    start: int
    end: int
    sig: str = ""
    doc: str = ""
    decorators: list[str] = field(default_factory=list)
    is_async: bool = False
    bases: list[str] = field(default_factory=list)
    children: list["Node"] = field(default_factory=list)
    parent: "Node | None" = field(default=None, repr=False)
    raw_calls: list[str] = field(default_factory=list)
    raw_refs: list[str] = field(default_factory=list)
    types: dict[str, str] = field(default_factory=dict)
    calls: list[str] = field(default_factory=list)
    callers: list[str] = field(default_factory=list)
    external: list[str] = field(default_factory=list)
    error: str = ""

    @property
    def lines(self) -> int:
        return self.end - self.start + 1

    def walk(self):
        yield self
        for c in self.children:
            yield from c.walk()


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
    return any(isinstance(s, ast.Name) and s.id == "__name__" for s in sides) and \
        any(isinstance(s, ast.Constant) and s.value == "__main__" for s in sides)


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
    if isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant) and isinstance(st.value.value, str):
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
        elif isinstance(n, (ast.Assign, ast.AnnAssign)) and isinstance(n.value, ast.Call):
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
        return (first if len(first) <= 50 else first[:49] + "…") + (" …" if len(stmts) > 1 else "")
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
        self.root = Node(id=rel, kind="module", name=PurePosixPath(rel).name, qual="",
                         file=rel, start=1, end=max(1, len(self.lines)))
        try:
            tree = ast.parse(src, filename=rel)
        except SyntaxError as e:
            self.root.error = f"SyntaxError line {e.lineno}: {e.msg}"
            return
        self.root.doc = first_line(ast.get_docstring(tree))
        self._imports(tree)
        self.root.children = self._segment(tree.body, self.root, in_class=False, prev_end=0)

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
                    self.dep_specs.append((mod, a.name if a.name != "*" else None, n.level))
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
        return Node(id=nid, kind=kind, name=name, qual=qual, file=self.rel, start=s, end=e, parent=parent)

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
                    gkind = "script" if any(category(g, in_class) == "script" for g in group) \
                        else ("attrs" if in_class else "globals")
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
            n = self._mk("method" if in_class else "def", st.name, parent, s, st.end_lineno, qual)
            n.is_async = isinstance(st, ast.AsyncFunctionDef)
            ret = f" -> {unparse(st.returns)}" if st.returns else ""
            n.sig = f"({unparse(st.args)}){ret}"
            n.children = [self._def(d, n, False, st.lineno) for d in direct_defs(st.body)]
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
            self.files[rel] = FileGraph(rel, p.read_text(encoding="utf-8", errors="replace"))
        self.nodes: dict[str, Node] = {n.id: n for fg in self.files.values() for n in fg.root.walk()}
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
            return self.descend(cls, parts[1:], depth + 1) if cls and len(parts) > 1 else None
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
                r = self.resolve_module(f"{mod}.{attr}" if attr and mod else (attr or mod), rel, level) \
                    if attr else None
                r = r or self.resolve_module(mod, rel, level)
                if r and r != rel:
                    ds.append(r)
            self.deps[rel] = sorted(set(ds))
            for d in self.deps[rel]:
                self.rdeps[d].append(rel)


    def find(self, target: str) -> list[Node]:
        def match_files(f):
            f = f.removeprefix("./")
            return [f] if f in self.files else [r for r in self.files if r.endswith("/" + f)]

        m = re.fullmatch(r"(.+\.py):(\d+)", target)
        if m or ("::" in target and target.split("::", 1)[1].isdigit()):
            f, line = (m.group(1), int(m.group(2))) if m else (target.split("::")[0], int(target.split("::")[1]))
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
            return [n for n in self.nodes.values() if n.file in rels and (n.qual == q or n.id.endswith("::" + q))]
        if target.endswith(".py"):
            return [self.files[r].root for r in match_files(target)]
        exact = [n for n in self.nodes.values() if n.qual == target]
        return exact or [n for n in self.nodes.values()
                         if n.kind in DEFS and (n.qual.endswith("." + target) or n.name == target)]

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
            d = {"id": n.id, "k": n.kind, "n": n.name, "q": n.qual, "s": n.start, "e": n.end}
            for key, val in (("sig", n.sig), ("doc", n.doc), ("dec", n.decorators), ("a", n.is_async),
                             ("c", n.calls), ("b", n.callers), ("x", n.external[:12]), ("err", n.error),
                             ("ch", [nd(c) for c in n.children])):
                if val:
                    d[key] = val
            return d

        data = {
            "root": str(self.root),
            "generated": datetime.now().isoformat(timespec="seconds"),
            "stats": self.stats(),
            "files": [{"path": rel, "deps": self.deps[rel], "rdeps": sorted(self.rdeps[rel]),
                       "root": nd(fg.root)} for rel, fg in sorted(self.files.items())],
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


def render_map(proj: Project, depth: int = 99, calls: bool = True, external: bool = False) -> str:
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
                extra.append("→ " + ", ".join(names[:6]) + (f" +{len(names) - 6}" if len(names) > 6 else ""))
            if external and n.external:
                extra.append("⋯ " + ", ".join(n.external[:5]) + (" …" if len(n.external) > 5 else ""))
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
        head.append("# boxes: " + ", ".join(f"{c.name}[{c.start}-{c.end}]" for c in n.children[:20]))
    if n.calls:
        head.append("# calls: " + ", ".join(ref_name(proj, t, n) for t in n.calls))
    if n.callers:
        head.append("# called by: " + ", ".join(ref_name(proj, t, n) for t in n.callers))
    w = len(str(n.end))
    body = [f"{i:>{w}} | {fg.lines[i - 1]}" for i in range(n.start, min(n.end, len(fg.lines)) + 1)]
    return "\n".join(head + body)


def render_html(proj: Project, with_source: bool = True, start: str | None = None) -> str:
    data = proj.to_dict(with_source)
    data["start"] = start
    blob = json.dumps(data, separators=(",", ":")).replace("<", "\\u003c")
    return HTML.replace("__EPY_TITLE__", html.escape(proj.root.name)).replace("__EPY_DATA__", blob)


HTML = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>epy · __EPY_TITLE__</title>
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=JetBrains+Mono:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--bg:#f5f5f2;--surface:#fff;--surface2:#efefeb;--line:#e3e3de;--line2:#d2d2cb;--ink:#1b1b19;--ink2:#3d3d38;--mute:#72726b;--faint:#a6a69e;
--accent:#4a61e0;--accent-soft:#e8ebfc;--caller:#c9620e;--caller-soft:#fbede0;--codebg:#fbfbf9;--hv:#f1efe8;--dot:#d8d8d0;--hub:#1d1d1b;--hub-ink:#f7f7f4;
--shadow:0 1px 2px rgb(24 24 20/.05),0 4px 14px rgb(24 24 20/.06);--shadow-lg:0 2px 6px rgb(24 24 20/.07),0 14px 36px rgb(24 24 20/.12);
--k-class:#7c4fe8;--k-def:#2f66d6;--k-method:#0f8a80;--k-imports:#85857e;--k-globals:#a8700c;--k-attrs:#a8700c;--k-main:#c93a78;--k-script:#5f6b7c;--k-doc:#7d8c6c;--k-module:#1b1b19;
--t-k:#a0359b;--t-s:#2e7a31;--t-c:#9b9b92;--t-n:#ad5f0c;--t-f:#2750c4;--t-b:#0b7690;--t-d:#9e6600;--t-self:#c03b3b;
--mono:"JetBrains Mono",ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;--sans:Inter,system-ui,-apple-system,"Segoe UI",sans-serif;
--lw:264px;--rw:min(560px,36vw)}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){--bg:#0f0f11;--surface:#17171a;--surface2:#1f1f23;--line:#2a2a2f;--line2:#38383e;--ink:#ececee;--ink2:#c8c8ce;--mute:#8e8e97;--faint:#5e5e66;
--accent:#8b9cff;--accent-soft:#222849;--caller:#f2a25a;--caller-soft:#38291a;--codebg:#131316;--hv:#1f1f24;--dot:#24242a;--hub:#ececee;--hub-ink:#141416;
--shadow:0 1px 2px rgb(0 0 0/.4),0 6px 18px rgb(0 0 0/.3);--shadow-lg:0 2px 6px rgb(0 0 0/.5),0 16px 40px rgb(0 0 0/.45);
--k-class:#b39cff;--k-def:#7aa7ff;--k-method:#4fd1c2;--k-imports:#8e8e97;--k-globals:#e0b04a;--k-attrs:#e0b04a;--k-main:#f27aae;--k-script:#98a2b3;--k-doc:#a8b597;--k-module:#ececee;
--t-k:#c792ea;--t-s:#a5d68a;--t-c:#6c6c76;--t-n:#f2a66b;--t-f:#82aaff;--t-b:#6fd3e0;--t-d:#e7c068;--t-self:#f07178}}
:root[data-theme="dark"]{--bg:#0f0f11;--surface:#17171a;--surface2:#1f1f23;--line:#2a2a2f;--line2:#38383e;--ink:#ececee;--ink2:#c8c8ce;--mute:#8e8e97;--faint:#5e5e66;
--accent:#8b9cff;--accent-soft:#222849;--caller:#f2a25a;--caller-soft:#38291a;--codebg:#131316;--hv:#1f1f24;--dot:#24242a;--hub:#ececee;--hub-ink:#141416;
--shadow:0 1px 2px rgb(0 0 0/.4),0 6px 18px rgb(0 0 0/.3);--shadow-lg:0 2px 6px rgb(0 0 0/.5),0 16px 40px rgb(0 0 0/.45);
--k-class:#b39cff;--k-def:#7aa7ff;--k-method:#4fd1c2;--k-imports:#8e8e97;--k-globals:#e0b04a;--k-attrs:#e0b04a;--k-main:#f27aae;--k-script:#98a2b3;--k-doc:#a8b597;--k-module:#ececee;
--t-k:#c792ea;--t-s:#a5d68a;--t-c:#6c6c76;--t-n:#f2a66b;--t-f:#82aaff;--t-b:#6fd3e0;--t-d:#e7c068;--t-self:#f07178}
.t-k{color:var(--t-k)}.t-s{color:var(--t-s)}.t-c{color:var(--t-c);font-style:italic}.t-n{color:var(--t-n)}.t-f{color:var(--t-f);font-weight:600}.t-b{color:var(--t-b)}.t-d{color:var(--t-d)}.t-self{color:var(--t-self)}
.k-class{--kc:var(--k-class)}.k-def{--kc:var(--k-def)}.k-method{--kc:var(--k-method)}.k-imports{--kc:var(--k-imports)}.k-globals{--kc:var(--k-globals)}.k-attrs{--kc:var(--k-attrs)}.k-main{--kc:var(--k-main)}.k-script{--kc:var(--k-script)}.k-doc{--kc:var(--k-doc)}.k-module{--kc:var(--k-module)}

*{box-sizing:border-box}html,body{margin:0;height:100%}
body{background:var(--bg);color:var(--ink);font:13px/1.5 var(--sans);-webkit-font-smoothing:antialiased;height:100vh;overflow:hidden;display:grid;
  grid-template-rows:50px minmax(0,1fr);grid-template-columns:var(--lw) 1px minmax(0,1fr) 1px var(--rw);grid-template-areas:"top top top top top" "side g1 main g2 code"}
body.noside{--lw:0px}body.nocode{--rw:0px}body.noside aside,body.noside .gut[data-gut=l],body.nocode #code,body.nocode .gut[data-gut=r]{display:none}
svg.i{width:16px;height:16px;fill:none;stroke:currentColor;stroke-width:1.5;stroke-linecap:round;stroke-linejoin:round;flex:none}
button{font:inherit;color:inherit}
.ib{display:inline-grid;place-items:center;width:30px;height:30px;border:0;border-radius:7px;background:transparent;color:var(--mute);cursor:pointer}
.ib:hover{background:var(--surface2);color:var(--ink)}.ib.sm{width:24px;height:24px}
.ib.on{color:var(--ink)}
.btn{font:500 12px var(--sans);padding:5px 10px;border:1px solid var(--line);border-radius:7px;background:var(--surface);color:var(--ink);cursor:pointer;white-space:nowrap}
.btn:hover{border-color:var(--line2);background:var(--surface2)}
kbd{font:11px var(--mono);color:var(--faint);border:1px solid var(--line);border-radius:4px;padding:0 5px;background:var(--surface)}

/* top bar */
header{grid-area:top;display:flex;align-items:center;gap:8px;padding:0 10px;background:var(--surface);border-bottom:1px solid var(--line);min-width:0}
.brand{display:flex;align-items:center;gap:8px;color:var(--ink);text-decoration:none;font:700 15px var(--sans);letter-spacing:-.01em;margin-right:6px}
.logo{display:grid;place-items:center;width:24px;height:24px;border-radius:7px;background:var(--hub);color:var(--hub-ink);font:700 13px var(--mono)}
.crumbs{display:flex;align-items:center;gap:2px;min-width:0;overflow:hidden;white-space:nowrap;font:500 13px var(--sans);color:var(--mute)}
.crumbs a{color:var(--mute);text-decoration:none;padding:3px 5px;border-radius:5px;cursor:pointer}.crumbs a:hover{background:var(--surface2);color:var(--ink)}
.crumbs .cur{color:var(--ink);font-weight:600}.crumbs .sl{color:var(--faint)}
.grow{flex:1}
.stats{color:var(--mute);font-size:12px;white-space:nowrap}
.search{display:flex;align-items:center;gap:7px;width:280px;height:32px;padding:0 9px;border:1px solid var(--line);border-radius:8px;background:var(--bg);color:var(--mute)}
.search:focus-within{border-color:var(--accent);box-shadow:0 0 0 3px var(--accent-soft)}
#q{flex:1;min-width:0;border:0;outline:0;background:transparent;color:var(--ink);font:13px var(--sans)}

/* panes */
aside{grid-area:side;display:flex;flex-direction:column;min-height:0;background:var(--surface)}
main{grid-area:main;position:relative;overflow:auto;min-width:0}
#code{grid-area:code;display:flex;flex-direction:column;min-height:0;min-width:0;background:var(--surface)}
.gut{position:relative;background:var(--line);z-index:6}.gut[data-gut=l]{grid-area:g1}.gut[data-gut=r]{grid-area:g2}
.gut::after{content:"";position:absolute;inset:0 -4px;cursor:col-resize}.gut:hover,.gut.drag{background:var(--accent)}
.phead{display:flex;align-items:center;gap:8px;padding:0 10px 0 14px;height:38px;flex:none;border-bottom:1px solid var(--line);font:600 11px var(--sans);letter-spacing:.06em;text-transform:uppercase;color:var(--mute)}
.phead .ct{font:500 11px var(--mono);letter-spacing:0;text-transform:none;color:var(--faint)}

/* explorer tree */
.tree{flex:1;overflow:auto;padding:6px 0 24px}
.tr{position:relative;display:flex;align-items:center;gap:6px;height:26px;padding:0 10px 0 calc(8px + var(--d) * 14px);cursor:pointer;color:var(--ink2);font:13px var(--sans);white-space:nowrap;user-select:none}
.tr:hover{background:var(--surface2)}
.tr .nm{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis}.tr .ct{font:11px var(--mono);color:var(--faint)}
.tr .chev{transition:transform .12s;color:var(--faint)}.tr.open .chev{transform:rotate(90deg)}.tr .chev.sp{visibility:hidden}
.tr.dir{color:var(--ink);font-weight:500}.tr.dir .fold{color:var(--mute)}
.tr.on{background:var(--accent-soft);color:var(--ink);font-weight:600}.tr.on::before{content:"";position:absolute;left:0;top:4px;bottom:4px;width:3px;border-radius:0 3px 3px 0;background:var(--accent)}
.grp{position:relative}.grp::before{content:"";position:absolute;top:0;bottom:4px;left:calc(15px + var(--d) * 14px);width:1px;background:var(--line)}
.pyb{display:inline-grid;place-items:center;height:15px;padding:0 4px;border-radius:4px;background:color-mix(in srgb,var(--k-def) 14%,transparent);color:var(--k-def);font:600 9px var(--mono);letter-spacing:.02em}
.res h5{margin:12px 14px 4px;font:600 11px var(--sans);letter-spacing:.06em;text-transform:uppercase;color:var(--mute)}
.res .tr{--d:0;padding-left:14px}.res .tr .q{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;font:12px var(--mono);color:var(--ink)}
.empty{padding:6px 14px;color:var(--faint)}

/* kind pills */
.kp{display:inline-flex;align-items:center;height:18px;padding:0 6px;border-radius:5px;background:color-mix(in srgb,var(--kc) 13%,transparent);color:var(--kc);font:600 11px var(--mono);white-space:nowrap}
.cin,.cout{display:inline-flex;align-items:center;height:18px;padding:0 6px;border-radius:9px;font:600 11px var(--mono)}
.cin{background:var(--caller-soft);color:var(--caller)}.cout{background:var(--accent-soft);color:var(--accent)}

/* overview */
.ov{padding:28px 32px 60px;max-width:1500px}
.hero h1{margin:0;font:700 24px var(--sans);letter-spacing:-.02em}.hero p{margin:2px 0 18px;color:var(--mute);font:12px var(--mono)}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px;margin-bottom:16px}
.tile{background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:12px 14px}.tile b{display:block;font:700 22px var(--sans);letter-spacing:-.02em}.tile span{color:var(--mute);font-size:12px}
.legend{display:flex;flex-wrap:wrap;gap:6px;margin:0 0 26px}
.osec{margin:0 0 28px}.osec h3{display:flex;align-items:center;gap:8px;margin:0 0 10px;font:600 13px var(--mono);color:var(--ink2)}.osec h3 span{color:var(--faint);font-weight:400}
.cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(230px,1fr));gap:12px}
.card{all:unset;box-sizing:border-box;cursor:pointer;background:var(--surface);border:1px solid var(--line);border-radius:12px;padding:12px 14px;display:flex;flex-direction:column;gap:9px;transition:border-color .12s,box-shadow .12s,transform .12s}
.card:hover{border-color:var(--line2);box-shadow:var(--shadow);transform:translateY(-1px)}.card:focus-visible{outline:2px solid var(--accent)}
.ct2{display:flex;justify-content:space-between;align-items:center;gap:8px}.ct2 b{font:600 13px var(--mono);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.ct2 span{color:var(--faint);font:11px var(--mono);white-space:nowrap;flex:none}
.strip{display:flex;height:6px;border-radius:3px;overflow:hidden;gap:2px}.strip i{min-width:3px;border-radius:2px}
.cm{color:var(--mute);font-size:11.5px}.cd{color:var(--mute);font-size:12px;line-height:1.4;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.err{color:var(--caller);font:12px var(--mono)}

/* mind map */
body.mapmode main{overflow:hidden}
.mmview{position:absolute;inset:0;overflow:hidden;cursor:grab;touch-action:none;background-image:radial-gradient(circle,var(--dot) 1.1px,transparent 1.3px)}
.mmview.panning{cursor:grabbing}
.mmworld{position:absolute;left:0;top:0;transform-origin:0 0}.mmworld.anim{transition:transform .35s cubic-bezier(.2,.7,.2,1)}
.mmsvg{position:absolute;left:0;top:0;width:1px;height:1px;overflow:visible;pointer-events:none}.mmsvg.top{z-index:3}
#mmnodes{position:absolute;left:0;top:0}
.mm{position:absolute;left:0;top:0;width:max-content;min-width:230px;max-width:660px;background:var(--surface);border:1px solid var(--line);border-radius:11px;box-shadow:var(--shadow);cursor:pointer;z-index:1;transition:box-shadow .15s,border-color .15s}
.mm::before{content:"";position:absolute;left:10px;right:10px;top:-1px;height:3px;border-radius:0 0 3px 3px;background:var(--bc)}
.mm:hover{box-shadow:var(--shadow-lg);border-color:var(--line2)}
.mm .mh{display:flex;align-items:center;gap:7px;padding:10px 12px 9px;font:13px var(--mono);white-space:nowrap}
.mm .nm{font-weight:600;color:var(--ink)}.mm .sig{color:var(--mute);max-width:380px;overflow:hidden;text-overflow:ellipsis;font-size:12px}
.mm .sp{margin-left:auto;padding-left:12px;color:var(--faint);font-size:11px}
.mm .mc{max-height:380px;overflow:auto;border-top:1px solid var(--line);background:var(--codebg);font:12px/1.6 var(--mono);padding:6px 0 8px;cursor:text;border-radius:0 0 11px 11px}
.mm .mc .cl{display:flex;white-space:pre;padding-right:16px}.mm .mc .g{flex:none;width:3.4em;padding-right:12px;text-align:right;color:var(--faint);user-select:none}
.mm.sel{border-color:var(--accent);box-shadow:0 0 0 3px var(--accent-soft),var(--shadow-lg);z-index:2}
.mm.callee{border-color:var(--accent);border-style:dashed}.mm.caller{border-color:var(--caller);border-style:dashed}
.mm.root{min-width:0;max-width:360px;background:var(--hub);color:var(--hub-ink);border:0;border-radius:14px;box-shadow:var(--shadow-lg);z-index:2;padding:4px 4px 8px}
.mm.root::before{display:none}.mm.root .mh{font:700 18px var(--sans);letter-spacing:-.01em;gap:10px;padding:10px 14px 2px}
.mm.root .sp{color:color-mix(in srgb,var(--hub-ink) 55%,transparent);font:500 11px var(--mono)}
.mm.root .rs{padding:0 14px;font:12px var(--sans);color:color-mix(in srgb,var(--hub-ink) 70%,transparent);white-space:normal}
.knob{position:absolute;top:10px;min-width:22px;height:22px;padding:0 6px;border-radius:11px;border:2px solid var(--bc);background:var(--surface);color:var(--ink);font:600 11px/18px var(--mono);cursor:pointer;z-index:2;box-shadow:var(--shadow)}
.knob:hover{background:var(--bc);color:#fff}
.side-r>.knob{right:-13px}.side-l>.knob{left:-13px}
.names .mm:not(.root):not(.open){background:transparent;border-color:transparent;box-shadow:none;min-width:0}.names .mm:not(.root):not(.open)::before{display:none}
.names .mm:not(.root):not(.open) .mh{font:500 14px var(--sans);padding:3px 8px}.names .mm:not(.root):not(.open):hover{background:var(--surface)}
.names .mm:not(.root):not(.open) .nm{color:color-mix(in srgb,var(--bc) 60%,var(--ink))}
.names .mm.blk:not(.open) .mh{font-size:12.5px}.names .mm:not(.open)>.knob{top:4px}.names .mm.open{z-index:2}
.names .mm.sel{background:var(--surface)}
.toolbar{position:absolute;z-index:5;left:50%;bottom:16px;transform:translateX(-50%);display:flex;align-items:center;gap:4px;padding:5px;background:color-mix(in srgb,var(--surface) 88%,transparent);backdrop-filter:blur(10px);border:1px solid var(--line);border-radius:12px;box-shadow:var(--shadow-lg);white-space:nowrap}
.toolbar .sep{width:1px;height:20px;background:var(--line);margin:0 4px}
.seg{display:inline-flex;padding:2px;background:var(--surface2);border-radius:8px}
.seg button{border:0;background:transparent;padding:4px 10px;border-radius:6px;font:500 12px var(--sans);color:var(--mute);cursor:pointer}
.seg button.on{background:var(--surface);color:var(--ink);box-shadow:0 1px 2px rgb(0 0 0/.12)}
.tbtn{border:0;background:transparent;padding:5px 9px;border-radius:7px;font:500 12px var(--sans);color:var(--ink2);cursor:pointer}.tbtn:hover{background:var(--surface2)}
.zl{min-width:44px;text-align:center;font:500 11px var(--mono);color:var(--mute)}
.hint{position:absolute;z-index:4;left:14px;bottom:18px;display:flex;gap:10px;font:11px var(--sans);color:var(--mute)}
.hint span{display:flex;align-items:center;gap:5px}.hint i{width:16px;border-top:2px dashed currentColor}

/* outline view */
.ol{padding:22px 26px 60px;max-width:1100px}
.olh{display:flex;align-items:center;gap:10px;margin-bottom:16px}.olh h2{margin:0;font:600 17px var(--mono)}.olh .grow{flex:1}
.flow{position:relative;padding-right:120px}
#edges{position:absolute;left:0;top:0;pointer-events:none;overflow:visible}
.box{position:relative;min-width:0;background:var(--surface);border:1px solid var(--line);border-left:3px solid var(--kc);border-radius:8px;margin:0 0 6px;cursor:pointer}
.box:hover{border-color:var(--line2);border-left-color:var(--kc)}.box.sel{box-shadow:0 0 0 3px var(--accent-soft);border-color:var(--accent);border-left-color:var(--kc)}
.box.callee{border-style:dashed;border-color:var(--accent);border-left-style:solid}.box.caller{border-style:dashed;border-color:var(--caller);border-left-style:solid}
.bh{display:flex;align-items:center;gap:8px;padding:7px 10px 5px;font:12.5px var(--mono);min-width:0}
.bh .nm{font-weight:600}.bh .sig{color:var(--mute);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;min-width:0;flex:1}
.bh .sp{color:var(--faint);white-space:nowrap;margin-left:auto;font-size:11px}
.track{position:relative;height:3px;margin:0 10px 7px;background:var(--surface2);border-radius:2px}.track i{position:absolute;top:0;bottom:0;background:var(--kc);border-radius:2px;opacity:.7}
.blk{background:transparent}.blk .bh{padding:5px 10px 3px;font-size:11.5px}
.kids{padding:0 8px 2px 16px}

/* code pane */
#ch{gap:8px;text-transform:none;letter-spacing:0;font:500 13px var(--sans);color:var(--ink)}
#ch b{font:600 13px var(--mono);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}#ch .ct{margin-left:auto}
.insp{flex:none;max-height:46%;overflow:auto;border-bottom:1px solid var(--line);padding:14px 16px 12px}
.insp:empty{display:none}
.ih{display:flex;align-items:center;gap:8px;flex-wrap:wrap}.ih b{font:600 14px var(--mono);word-break:break-all}
.ih .rng{color:var(--faint);font:11px var(--mono)}.ih .btn{margin-left:auto}
.sigf{margin:10px 0 0;padding:8px 10px;background:var(--surface2);border-radius:8px;font:12px/1.5 var(--mono);white-space:pre-wrap;word-break:break-word;color:var(--ink2)}
.doc{margin:8px 0 0;color:var(--mute)}
.rel{display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-top:12px}
.rel h5,.insp h5{margin:0 0 5px;font:600 11px var(--sans);letter-spacing:.06em;text-transform:uppercase;color:var(--mute)}
.lk{display:flex;gap:6px;align-items:baseline;font:12px var(--mono);color:var(--accent);cursor:pointer;padding:2px 0;overflow-wrap:anywhere}.lk:hover{text-decoration:underline}
.lk.in{color:var(--caller)}.lk small{color:var(--faint);font-size:11px;flex:none}
.chips{display:flex;flex-wrap:wrap;gap:5px;align-items:center}
.chip{font:11.5px var(--mono);padding:2px 8px;border:1px solid var(--line);border-radius:999px;cursor:pointer;color:var(--ink2);background:var(--surface)}.chip:hover{border-color:var(--accent);color:var(--accent)}
.xs{display:flex;flex-wrap:wrap;gap:4px;margin-top:6px}.xs code{font:11px var(--mono);padding:1px 6px;background:var(--surface2);border-radius:4px;color:var(--mute)}
details.ext{margin-top:12px}details.ext summary{cursor:pointer;font:600 11px var(--sans);letter-spacing:.06em;text-transform:uppercase;color:var(--mute)}
.intro p{margin:0 0 10px;color:var(--ink2)}.intro h5{margin:16px 0 6px}
.src{position:relative;flex:1;overflow:auto;background:var(--codebg);font:12.5px/1.65 var(--mono);padding:6px 0 40px}
.srcin{display:inline-block;min-width:100%}
.ln{display:flex;white-space:pre;cursor:pointer;padding-right:18px}
.ln .g{flex:none;position:sticky;left:0;width:4.4em;padding-right:14px;text-align:right;color:var(--faint);user-select:none;background:var(--codebg);border-left:3px solid var(--gc,transparent)}
.ln:hover .g{color:var(--ink2)}
.ln.hv{background:var(--hv)}.ln.hv .g{background:var(--hv)}
.ln.hl{background:color-mix(in srgb,var(--hc) 11%,var(--codebg))}.ln.hl .g{background:color-mix(in srgb,var(--hc) 16%,var(--codebg));color:var(--ink2)}
.nosrc{padding:16px;color:var(--mute)}

@media (max-width:900px){
  body{display:flex;flex-direction:column;height:auto;overflow:auto}
  header{position:sticky;top:0;z-index:10;height:50px;flex:none;gap:4px}.stats,.crumbs,kbd,.brand span+*{display:none}.brand{font-size:0;gap:0;margin:0}.search{flex:1;width:auto;min-width:0}
  aside{max-height:38vh;border-bottom:1px solid var(--line)}.gut{display:none}
  main{height:72vh;flex:none;border-bottom:1px solid var(--line)}body:not(.mapmode) main{height:auto;overflow:visible}
  #code{min-height:60vh}.src{max-height:70vh}
  body.noside aside,body.nocode #code{display:none}
  .toolbar{bottom:10px;max-width:calc(100% - 20px);overflow-x:auto}.hint{display:none}
  .ov,.ol{padding:18px 16px 40px}.flow{padding-right:50px}.bh{flex-wrap:wrap}.bh .sig{flex-basis:100%;order:5}
}
</style></head><body>
<header>
  <button class="ib" data-toggle="side" title="Toggle explorer"><svg class="i" viewBox="0 0 16 16"><rect x="1.5" y="2.5" width="13" height="11" rx="2"/><path d="M6 2.5v11"/></svg></button>
  <a class="brand" href="#"><span class="logo">e</span>epy</a>
  <nav class="crumbs" id="crumbs"></nav>
  <div class="grow"></div>
  <span class="stats" id="stats"></span>
  <label class="search"><svg class="i" viewBox="0 0 16 16"><circle cx="7" cy="7" r="4.5"/><path d="M10.5 10.5L14 14"/></svg><input id="q" placeholder="Search files and functions" autocomplete="off" spellcheck="false"><kbd>/</kbd></label>
  <button class="ib" data-theme-toggle title="Theme"><svg class="i" viewBox="0 0 16 16"><circle cx="8" cy="8" r="5.5"/><path d="M8 2.5a5.5 5.5 0 0 0 0 11z" fill="currentColor"/></svg></button>
  <button class="ib" data-toggle="code" title="Toggle code pane"><svg class="i" viewBox="0 0 16 16"><rect x="1.5" y="2.5" width="13" height="11" rx="2"/><path d="M10 2.5v11"/></svg></button>
</header>
<aside id="side"><div class="phead"><span>Explorer</span><span class="ct" id="fcount"></span><span class="grow"></span>
  <button class="ib sm" data-act="tree-collapse" title="Collapse folders"><svg class="i" viewBox="0 0 16 16"><path d="M4 6l4-3 4 3M4 10l4 3 4-3"/></svg></button></div><div class="tree" id="tree"></div></aside>
<div class="gut" data-gut="l"></div>
<main id="main"></main>
<div class="gut" data-gut="r"></div>
<section id="code"><div class="phead" id="ch"></div><div class="insp" id="insp"></div><div class="src" id="src"></div></section>
<script type="application/json" id="epy-data">__EPY_DATA__</script>
<script>
const D = JSON.parse(document.getElementById('epy-data').textContent);
const $ = (s, el = document) => el.querySelector(s);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const store = { get(k, d) { try { const v = localStorage.getItem(k); return v === null ? d : v; } catch (e) { return d; } }, set(k, v) { try { localStorage.setItem(k, v); } catch (e) {} } };
const DEFS = new Set(['class', 'def', 'method']);
const KINDS = ['class', 'def', 'method', 'imports', 'globals', 'main', 'script', 'doc'];
const PAL = ['#e5736b', '#5f9be6', '#79bf5f', '#cf7fd6', '#36b89c', '#9585e0', '#ec9548', '#c9a524'];
const ICON = {
  chev: '<svg class="i chev" viewBox="0 0 16 16"><path d="M6 4l4 4-4 4"/></svg>',
  chevsp: '<svg class="i chev sp" viewBox="0 0 16 16"><path d="M6 4l4 4-4 4"/></svg>',
  folder: '<svg class="i fold" viewBox="0 0 16 16"><path d="M1.5 4.5a1 1 0 0 1 1-1h3.3l1.5 1.5h6.2a1 1 0 0 1 1 1v6.5a1 1 0 0 1-1 1h-11a1 1 0 0 1-1-1z"/></svg>',
  fit: '<svg class="i" viewBox="0 0 16 16"><path d="M2 6V2h4M10 2h4v4M14 10v4h-4M6 14H2v-4"/></svg>',
};

const byId = new Map(), files = new Map(), fstat = new Map(), srcCache = new Map();
function idx(n, f, p) { n.f = f; n.p = p; byId.set(n.id, n); (n.ch || []).forEach(c => idx(c, f, n)); }
D.files.forEach(f => { files.set(f.path, f); idx(f.root, f.path, null); fstat.set(f.path, { cls: 0, fns: 0 }); });
for (const n of byId.values()) { if (n.k === 'class') fstat.get(n.f).cls++; else if (n.k === 'def' || n.k === 'method') fstat.get(n.f).fns++; }
const stem = p => p.split('/').pop().replace(/\.py$/, '');
const base = p => p.split('/').pop();
const dirOf = p => p.includes('/') ? p.slice(0, p.lastIndexOf('/')) : '.';
const kwOf = n => n.k === 'class' ? 'class' : DEFS.has(n.k) ? (n.a ? 'async def' : 'def') : n.k === 'module' ? 'file' : n.k;
const nlines = n => n.e - n.s + 1;
const pq = q => q.replace(/<(\w+)@(\d+)>/g, '$1 L$2');
const nameOf = (n, here) => (n.k === 'module' ? n.f : (n.f === here ? pq(n.q) : stem(n.f) + ':' + pq(n.q)));
const srcLines = f => { if (!D.src || !(f in D.src)) return null; if (!srcCache.has(f)) srcCache.set(f, D.src[f].split('\n')); return srcCache.get(f); };
const shortSig = (n, w = 60) => { let s = n.sig || ''; if (n.k === 'method') s = s.replace(/^\((self|cls)(, )?/, '('); return s.length > w ? s.slice(0, w - 2) + '…)' : s; };
const plural = (n, w) => `${n.toLocaleString()} ${w}${n === 1 ? '' : 's'}`;
function colorOf(n) {
  let a = n; while (a.p && a.p.k !== 'module') a = a.p;
  if (!a.p) return 'var(--ink)';
  return PAL[a.p.ch.indexOf(a) % PAL.length];
}
function innermost(f, line) {
  let best = files.get(f).root;
  for (;;) { const c = (best.ch || []).find(c => c.s <= line && line <= c.e); if (!c) return best; best = c; }
}

const S = D.stats, ROOTNAME = D.root.split('/').filter(Boolean).pop() || D.root;
$('#stats').textContent = `${plural(S.files, 'file')} · ${S.lines.toLocaleString()} lines · ${plural(S.edges, 'call link')}`;
$('#fcount').textContent = S.files;

function go(f, n) { const h = 'f=' + encodeURIComponent(f || '') + (n ? '&n=' + encodeURIComponent(n) : ''); if (location.hash.slice(1) === h) render(); else location.hash = h; }
function state() { const h = new URLSearchParams(location.hash.slice(1)); return { file: h.get('f') || null, sel: h.get('n') || null }; }

// ── layout chrome: theme, pane toggles, resizable gutters ──
let THEME = store.get('epy.theme', 'auto');
function applyTheme() { if (THEME === 'auto') delete document.documentElement.dataset.theme; else document.documentElement.dataset.theme = THEME; }
applyTheme();
['side', 'code'].forEach(p => { if (store.get('epy.hide.' + p, '0') === '1') document.body.classList.add('no' + p); });
['lw', 'rw'].forEach(k => { const v = store.get('epy.' + k, ''); if (v) document.body.style.setProperty('--' + k, v); });
document.querySelectorAll('.gut').forEach(g => {
  g.addEventListener('pointerdown', e => {
    e.preventDefault(); g.setPointerCapture(e.pointerId); g.classList.add('drag');
    const left = g.dataset.gut === 'l';
    const move = ev => {
      const w = left ? ev.clientX : window.innerWidth - ev.clientX;
      const px = Math.max(left ? 180 : 280, Math.min(window.innerWidth * (left ? 0.4 : 0.6), w)) + 'px';
      document.body.style.setProperty(left ? '--lw' : '--rw', px); store.set(left ? 'epy.lw' : 'epy.rw', px);
    };
    const up = () => { g.classList.remove('drag'); g.removeEventListener('pointermove', move); g.removeEventListener('pointerup', up); };
    g.addEventListener('pointermove', move); g.addEventListener('pointerup', up);
  });
});

// ── explorer: nested folder tree (single-child folders compacted) ──
const OPEN = new Set(JSON.parse(store.get('epy.open', '[]')));
const saveOpen = () => store.set('epy.open', JSON.stringify([...OPEN]));
function buildTree() {
  const root = { name: '', path: '', dirs: new Map(), files: [] };
  for (const f of D.files) {
    const parts = f.path.split('/'); let node = root;
    for (let i = 0; i < parts.length - 1; i++) {
      if (!node.dirs.has(parts[i])) node.dirs.set(parts[i], { name: parts[i], path: parts.slice(0, i + 1).join('/'), dirs: new Map(), files: [] });
      node = node.dirs.get(parts[i]);
    }
    node.files.push(f);
  }
  const fin = n => {
    n.dirs = [...n.dirs.values()].map(fin).map(d => { while (!d.files.length && d.dirs.length === 1) { const c = d.dirs[0]; d = { ...c, name: d.name + '/' + c.name }; } return d; })
      .sort((a, b) => a.name.localeCompare(b.name));
    n.files.sort((a, b) => a.path.localeCompare(b.path));
    n.count = n.files.length + n.dirs.reduce((a, d) => a + d.count, 0);
    return n;
  };
  return fin(root);
}
const TREE = buildTree();
function treeHTML(node, depth, cur) {
  let h = '';
  for (const d of node.dirs) {
    const open = OPEN.has(d.path);
    h += `<div class="tr dir${open ? ' open' : ''}" data-dir="${esc(d.path)}" style="--d:${depth}">${ICON.chev}${ICON.folder}<span class="nm">${esc(d.name)}</span><span class="ct">${d.count}</span></div>`;
    if (open) h += `<div class="grp" style="--d:${depth}">${treeHTML(d, depth + 1, cur)}</div>`;
  }
  for (const f of node.files)
    h += `<div class="tr file${f.path === cur ? ' on' : ''}" data-f="${esc(f.path)}" style="--d:${depth}" title="${esc(f.path)}">${ICON.chevsp}<span class="pyb">py</span><span class="nm">${esc(base(f.path))}</span><span class="ct">${f.root.e}</span></div>`;
  return h;
}
function explorer(st) {
  const q = $('#q').value.trim().toLowerCase(), tree = $('#tree');
  if (q) {
    const fs = D.files.filter(f => f.path.toLowerCase().includes(q)).slice(0, 30);
    const ns = []; for (const n of byId.values()) { if (DEFS.has(n.k) && n.q.toLowerCase().includes(q)) { ns.push(n); if (ns.length >= 80) break; } }
    tree.innerHTML = `<div class="res"><h5>Files · ${fs.length}</h5>${fs.map(f => `<div class="tr" data-f="${esc(f.path)}"><span class="pyb">py</span><span class="q">${esc(f.path)}</span><span class="ct">${f.root.e}</span></div>`).join('') || '<div class="empty">No files</div>'}
      <h5>Functions · ${ns.length}${ns.length >= 80 ? '+' : ''}</h5>${ns.map(n => `<div class="tr k-${n.k}" data-go="${esc(n.id)}"><span class="kp">${n.k === 'class' ? 'class' : 'def'}</span><span class="q">${esc(n.q)}</span><span class="ct">${esc(stem(n.f))}:${n.s}</span></div>`).join('') || '<div class="empty">No functions</div>'}</div>`;
    return;
  }
  if (st.file) { const parts = st.file.split('/'); for (let i = 1; i < parts.length; i++) OPEN.add(parts.slice(0, i).join('/')); }
  tree.innerHTML = treeHTML(TREE, 0, st.file);
  const on = tree.querySelector('.tr.on');
  if (on) { const r = on.getBoundingClientRect(), t = tree.getBoundingClientRect(); if (r.top < t.top || r.bottom > t.bottom) on.scrollIntoView({ block: 'center' }); }
}
function crumbs(st) {
  let h = `<a data-home>${esc(ROOTNAME)}</a>`;
  if (st.file) {
    const parts = st.file.split('/');
    parts.forEach((p, i) => { h += `<span class="sl">/</span>` + (i === parts.length - 1 ? `<span class="cur">${esc(p)}</span>` : `<a data-dir="${esc(parts.slice(0, i + 1).join('/'))}">${esc(p)}</a>`); });
  }
  $('#crumbs').innerHTML = h;
}

// ── overview ──
function overview() {
  const dirs = new Map(); D.files.forEach(f => { const d = dirOf(f.path); if (!dirs.has(d)) dirs.set(d, []); dirs.get(d).push(f); });
  const tile = (v, l) => `<div class="tile"><b>${v.toLocaleString()}</b><span>${l}</span></div>`;
  $('#main').innerHTML = `<div class="ov"><div class="hero"><h1>${esc(ROOTNAME)}</h1><p>${esc(D.root)}</p>
    <div class="tiles">${tile(S.files, 'files')}${tile(S.lines, 'lines')}${tile(S.classes, 'classes')}${tile(S.functions, 'functions')}${tile(S.edges, 'call links')}</div>
    <div class="legend">${KINDS.map(k => `<span class="kp k-${k}">${k}</span>`).join('')}</div></div>
    ${[...dirs].map(([d, fs]) => `<section class="osec"><h3>${ICON.folder}${esc(d === '.' ? ROOTNAME : d)}<span>${fs.length}</span></h3><div class="cards">${fs.map(card).join('')}</div></section>`).join('')}</div>`;
}
function card(f) {
  const r = f.root, ch = r.ch || [], st = fstat.get(f.path);
  return `<button class="card" data-f="${esc(f.path)}"><div class="ct2"><b>${esc(base(f.path))}</b><span>${r.e} lines</span></div>
    <div class="strip">${ch.map((c, i) => `<i style="flex:${nlines(c)};background:${PAL[i % PAL.length]}" title="${esc(kwOf(c) + ' ' + (DEFS.has(c.k) ? c.n : '') + ' · ' + c.s + '–' + c.e)}"></i>`).join('')}</div>
    ${r.doc ? `<div class="cd">${esc(r.doc)}</div>` : ''}${r.err ? `<div class="err">${esc(r.err)}</div>` : ''}
    <div class="cm">${plural(st.cls, 'class').replace('classs', 'classes')} · ${plural(st.fns, 'function')}${f.deps.length ? ` · uses ${f.deps.length}` : ''}${f.rdeps.length ? ` · used by ${f.rdeps.length}` : ''}</div></button>`;
}

// ── python highlighter (whole file, so multi-line strings stay right) ──
const PYKW = new Set('and as assert async await break class continue def del elif else except finally for from global if import in is lambda nonlocal not or pass raise return try while with yield match case'.split(' '));
const PYCONST = new Set(['True', 'False', 'None']);
const PYBI = new Set('abs all any bool bytes callable dict dir enumerate filter float format getattr hasattr hash id input int isinstance issubclass iter len list map max min next object open ord pow print property range repr reversed round set setattr slice sorted staticmethod classmethod str sum super tuple type vars zip Exception ValueError KeyError TypeError IndexError RuntimeError AttributeError'.split(' '));
const TOKRE = /((?<!\w)[rRbBuUfF]{0,2}(?:"{3}[\s\S]*?(?:"{3}|$)|'{3}[\s\S]*?(?:'{3}|$)|"(?:\\.|[^"\\\n])*"?|'(?:\\.|[^'\\\n])*'?))|(#[^\n]*)|(@[A-Za-z_][\w.]*)|(\b\d[\d_]*(?:\.\d*)?(?:[eE][+-]?\d+)?j?\b)|([A-Za-z_]\w*)|(\n)|([^\n])/g;
const hlCache = new Map();
function hl(f) {
  if (hlCache.has(f)) return hlCache.get(f);
  if (!D.src || !(f in D.src)) return null;
  const lines = [[]]; let m, prev = '';
  const push = (c, text) => text.split('\n').forEach((p, i) => { if (i) lines.push([]); if (p) lines[lines.length - 1].push(c ? `<span class="t-${c}">${esc(p)}</span>` : esc(p)); });
  TOKRE.lastIndex = 0;
  while ((m = TOKRE.exec(D.src[f]))) {
    if (m[5]) {
      const w = m[5];
      const c = PYCONST.has(w) ? 'n' : PYKW.has(w) ? 'k' : (prev === 'def' || prev === 'class') ? 'f' : (w === 'self' || w === 'cls') ? 'self' : PYBI.has(w) ? 'b' : '';
      push(c, w); prev = w; continue;
    }
    if (m[6]) { lines.push([]); prev = ''; continue; }
    if (m[7] && /\s/.test(m[7])) { push('', m[7]); continue; }
    if (m[1]) push('s', m[1]); else if (m[2]) push('c', m[2]); else if (m[3]) push('d', m[3]); else if (m[4]) push('n', m[4]); else push('', m[7]);
    prev = '';
  }
  const out = lines.map(l => l.join(''));
  hlCache.set(f, out);
  return out;
}
function codeRows(f, s, e) {
  const H = hl(f); if (!H) return '';
  let out = '';
  for (let i = s; i <= e && i <= H.length; i++) out += `<div class="cl"><span class="g">${i}</span><span>${H[i - 1] || ' '}</span></div>`;
  return out;
}

// ── mind map: file in the middle, every block a code card on a branch ──
let MODE = store.get('epy.mode', 'map');
const MM = { file: null, disp: store.get('epy.disp', 'code'), T: [], byNode: new Map(), collapsed: new Set(), open: null, tx: 0, ty: 0, k: 1, drag: null, moved: false };

function mmCard(t) {
  const n = t.n, kids = (n.ch || []).length, col = MM.collapsed.has(n.id);
  if (t.depth === 0) {
    const st = fstat.get(n.f);
    return `<div class="mm root" data-id="${esc(n.id)}"><div class="mh"><span>${esc(base(n.f))}</span><span class="sp">${n.e} lines</span></div>
      <div class="rs">${plural(st.cls, 'class').replace('classs', 'classes')} · ${plural(st.fns, 'function')}</div>${n.err ? `<div class="rs err">${esc(n.err)}</div>` : ''}</div>`;
  }
  const blk = !DEFS.has(n.k), cin = (n.b || []).length, cout = (n.c || []).length;
  const showCode = D.src && (MM.disp === 'code' || n.id === MM.open);
  const title = blk
    ? `<span class="kp k-${n.k}">${esc(n.k)}</span>${!showCode && n.sig ? `<span class="sig">${esc(n.sig)}</span>` : ''}`
    : `<span class="kp k-${n.k}">${esc(kwOf(n))}</span><span class="nm">${esc(n.n)}</span>`;
  const own = n.k === 'class' && kids ? [n.s, Math.max(n.s, n.ch[0].s - 1)] : [n.s, n.e];
  const knob = kids ? `<button class="knob" data-knob="${esc(n.id)}" title="${col ? 'Expand' : 'Collapse'}">${col ? '+' + kids : '−'}</button>` : '';
  return `<div class="mm${blk ? ' blk' : ''}${n.id === MM.open ? ' open' : ''}" data-id="${esc(n.id)}" style="--bc:${t.color}"><div class="mh">${title}
    <span class="sp">${n.s}–${n.e}</span>${cin ? `<span class="cin" title="called from ${cin}">←${cin}</span>` : ''}${cout ? `<span class="cout" title="calls ${cout}">→${cout}</span>` : ''}</div>
    ${showCode ? `<div class="mc">${codeRows(n.f, own[0], own[1])}</div>` : ''}${knob}</div>`;
}

function modeSeg() {
  return `<div class="seg"><button class="${MODE === 'map' ? 'on' : ''}" data-mode="map">Map</button><button class="${MODE === 'outline' ? 'on' : ''}" data-mode="outline">Outline</button></div>`;
}
function mapView(path) {
  MM.file = path; MM.collapsed = new Set(); MM.open = null;
  let count = 0; for (const n of byId.values()) if (n.f === path) count++;
  if (count > 45 && MM.disp === 'code') for (const n of byId.values()) if (n.f === path && n.k === 'class') MM.collapsed.add(n.id);
  $('#main').innerHTML = `
    <div class="mmview${MM.disp === 'names' ? ' names' : ''}" id="mmview"><div class="mmworld" id="mmworld"><svg class="mmsvg" id="mmbr"></svg><div id="mmnodes"></div>
      <svg class="mmsvg top" id="mmcalls"><defs>
      <marker id="ma" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0L8,4L0,8z" fill="var(--accent)"/></marker>
      <marker id="mc" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0L8,4L0,8z" fill="var(--caller)"/></marker></defs><g></g></svg></div></div>
    <div class="hint"><span style="color:var(--accent)"><i></i>calls</span><span style="color:var(--caller)"><i></i>called by</span></div>
    <div class="toolbar">
      <div class="seg"><button class="${MM.disp === 'code' ? 'on' : ''}" data-disp="code">Code</button><button class="${MM.disp === 'names' ? 'on' : ''}" data-disp="names">Names</button></div>
      <span class="sep"></span>
      <button class="ib sm" data-act="zout" title="Zoom out">−</button><span class="zl" id="zl"></span><button class="ib sm" data-act="zin" title="Zoom in">+</button>
      <button class="ib sm" data-act="fit" title="Fit (f)">${ICON.fit}</button>
      <span class="sep"></span>
      <button class="tbtn" data-act="expand">Expand all</button><button class="tbtn" data-act="collapse">Collapse all</button>
      <span class="sep"></span>${modeSeg()}
    </div>`;
  bindView();
  mmLayout();
  mmFit(false);
}

function mmLayout() {
  const root = files.get(MM.file).root, nodesEl = $('#mmnodes');
  const T = [];
  const build = (n, depth, color, parent) => {
    const t = { n, depth, color, parent, kids: [] }; T.push(t);
    if (depth === 0 || !MM.collapsed.has(n.id)) (n.ch || []).forEach((c, i) => t.kids.push(build(c, depth + 1, depth === 0 ? PAL[i % PAL.length] : color, t)));
    return t;
  };
  const rt = build(root, 0, 'var(--ink)', null);
  nodesEl.innerHTML = T.map(mmCard).join('');
  const els = nodesEl.children;
  T.forEach((t, i) => { t.el = els[i]; t.w = t.el.offsetWidth; t.h = t.el.offsetHeight; t.hh = t.el.firstElementChild.offsetHeight; });
  const code = MM.disp === 'code', GX = code ? 72 : 48, GY = code ? 20 : 6, GC = code ? 68 : 42, COLMAX = code ? 1700 : 1300;
  // children of a node form a group; a tall group wraps into columns fed by a trunk
  const pack = kids => {
    const total = kids.reduce((a, k) => a + k.sub, 0) + GY * Math.max(0, kids.length - 1);
    const ncol = Math.max(1, Math.ceil(total / COLMAX)), target = total / ncol;
    const cols = [[]]; let h = 0;
    kids.forEach(k => {
      if (cols[cols.length - 1].length && h + k.sub > target * 1.08 && cols.length < ncol) { cols.push([]); h = 0; }
      cols[cols.length - 1].push(k); h += k.sub + GY;
    });
    const G = { cols: cols.map(c => ({ kids: c, w: Math.max(...c.map(k => k.sw)), h: c.reduce((a, k) => a + k.sub, 0) + GY * (c.length - 1) })) };
    G.wrapped = G.cols.length > 1;
    G.W = G.cols.reduce((a, c) => a + c.w, 0) + GC * (G.cols.length - 1);
    G.H = Math.max(...G.cols.map(c => c.h));
    return G;
  };
  const measure = t => {
    t.kids.forEach(measure);
    if (!t.kids.length) { t.sw = t.w; t.sub = t.h; return; }
    t.G = pack(t.kids); t.sw = t.w + GX + t.G.W; t.sub = Math.max(t.h, t.G.H);
  };
  rt.kids.forEach(measure);
  const total = rt.kids.reduce((a, t) => a + t.sub * t.sw, 0);
  const R = [], L = []; let acc = 0;
  rt.kids.forEach(t => { (acc + t.sub * t.sw / 2 < total / 2 ? R : L).push(t); acc += t.sub * t.sw; });
  rt.x = -rt.w / 2; rt.y = -rt.h / 2; rt.side = 0;
  const placeGroup = (G, side, x, top) => {
    G.top = top; let cx = x;
    G.cols.forEach(c => {
      c.inner = cx; let y = top;
      c.kids.forEach(k => { place(k, side, cx, y); y += k.sub + GY; });
      cx += side * (c.w + GC);
    });
  };
  const place = (t, side, x, top) => {
    t.side = side; t.x = side > 0 ? x : x - t.w; t.y = top + (t.sub - t.h) / 2;
    if (t.G) placeGroup(t.G, side, side > 0 ? t.x + t.w + GX : t.x - GX, top + (t.sub - t.G.H) / 2);
  };
  if (R.length) { rt.GR = pack(R); placeGroup(rt.GR, 1, rt.x + rt.w + GX * 1.7, -rt.GR.H / 2); }
  if (L.length) { rt.GL = pack(L); placeGroup(rt.GL, -1, rt.x - GX * 1.7, -rt.GL.H / 2); }
  T.forEach(t => { t.el.style.transform = `translate(${t.x}px,${t.y}px)`; t.el.classList.add(t.side < 0 ? 'side-l' : 'side-r'); });

  // branches: tapered curves, thick near the centre; wrapped groups get a trunk + stubs
  const WID = d => d === 1 ? [12, 5.5] : d === 2 ? [5.5, 3.2] : [3.2, 2.2];
  const ay = t => t.depth === 0 ? t.y + t.h / 2 : t.y + t.hh / 2;
  const outer = (p, s) => p.depth === 0 ? (s > 0 ? p.x + p.w - 12 : p.x + 12) : (s > 0 ? p.x + p.w : p.x);
  const inner = t => t.side > 0 ? t.x : t.x + t.w;
  let paths = '';
  const groups = [];
  if (rt.GR) groups.push([rt, rt.GR, 1]);
  if (rt.GL) groups.push([rt, rt.GL, -1]);
  T.forEach(t => { if (t.depth && t.G) groups.push([t, t.G, t.side]); });
  for (const [p, G, s] of groups) {
    const [wa, wb] = WID(p.depth + 1), x1 = outer(p, s), y1 = ay(p);
    if (!G.wrapped) {
      for (const t of G.cols[0].kids) {
        const x2 = inner(t), y2 = ay(t), a = wa / 2, b = wb / 2, mx = (x1 + x2) / 2;
        paths += `<path d="M${x1},${y1 - a}C${mx},${y1 - a} ${mx},${y2 - b} ${x2},${y2 - b}L${x2},${y2 + b}C${mx},${y2 + b} ${mx},${y1 + a} ${x1},${y1 + a}Z" fill="${t.color}" opacity=".85"/>`;
      }
      continue;
    }
    const trunkCol = p.depth === 0 ? 'var(--line2)' : p.color, yTop = G.top - 24;
    const xs = G.cols.map((c, j) => j === 0 ? (x1 + c.inner) / 2 : c.inner - s * GC / 2);
    const lastY = G.cols.map(c => ay(c.kids[c.kids.length - 1]));
    let d = `M${x1},${y1}H${xs[0]}M${xs[0]},${Math.min(yTop, y1)}V${Math.max(lastY[0], y1)}M${xs[0]},${yTop}H${xs[xs.length - 1]}`;
    xs.slice(1).forEach((x, j) => { d += `M${x},${yTop}V${lastY[j + 1]}`; });
    paths += `<path d="${d}" fill="none" stroke="${trunkCol}" stroke-width="${wb}" stroke-linecap="round" stroke-linejoin="round" opacity=".75"/>`;
    G.cols.forEach((c, j) => c.kids.forEach(t => {
      paths += `<path d="M${xs[j]},${ay(t)}H${inner(t)}" stroke="${t.color}" stroke-width="${wb}" stroke-linecap="round" opacity=".85"/>`;
    }));
  }
  $('#mmbr').innerHTML = paths;
  MM.T = T; MM.byNode = new Map(T.map(t => [t.n.id, t]));
}

function applyView(anim) {
  const w = $('#mmworld'), v = $('#mmview'); if (!w) return;
  w.classList.toggle('anim', !!anim);
  w.style.transform = `translate(${MM.tx}px,${MM.ty}px) scale(${MM.k})`;
  const g = 24 * MM.k; v.style.backgroundSize = `${g}px ${g}px`; v.style.backgroundPosition = `${MM.tx}px ${MM.ty}px`;
  const zl = $('#zl'); if (zl) zl.textContent = Math.round(MM.k * 100) + '%';
}
function mmFit(force) {
  const v = $('#mmview'), vw = v.clientWidth, vh = v.clientHeight;
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  MM.T.forEach(t => { x0 = Math.min(x0, t.x); y0 = Math.min(y0, t.y); x1 = Math.max(x1, t.x + t.w); y1 = Math.max(y1, t.y + t.h); });
  const k = Math.min(MM.disp === 'names' ? 1.4 : 1, (vw - 60) / (x1 - x0), (vh - 110) / (y1 - y0));
  if (k < 0.22 && !force) { MM.k = 0.5; MM.tx = vw / 2; MM.ty = vh / 2 - 20; }
  else { MM.k = Math.max(0.05, k); MM.tx = vw / 2 - (x0 + x1) / 2 * MM.k; MM.ty = (vh - 50) / 2 - (y0 + y1) / 2 * MM.k; }
  applyView(true);
}
function zoomAt(px, py, k, anim) {
  k = Math.min(2.5, Math.max(0.05, k));
  MM.tx = px - (px - MM.tx) * k / MM.k; MM.ty = py - (py - MM.ty) * k / MM.k; MM.k = k; applyView(anim);
}
function bindView() {
  const v = $('#mmview');
  v.addEventListener('wheel', e => {
    const mc = e.target.closest('.mc');
    if (mc && !e.ctrlKey && MM.k >= 0.6 && mc.scrollHeight > mc.clientHeight) {
      const atTop = mc.scrollTop <= 0 && e.deltaY < 0, atEnd = mc.scrollTop + mc.clientHeight >= mc.scrollHeight - 1 && e.deltaY > 0;
      if (!atTop && !atEnd) return;
    }
    e.preventDefault();
    const r = v.getBoundingClientRect();
    zoomAt(e.clientX - r.left, e.clientY - r.top, MM.k * Math.exp(-e.deltaY * (e.ctrlKey ? 0.01 : 0.0016)), false);
  }, { passive: false });
  v.addEventListener('pointerdown', e => {
    if (e.button !== 0 || e.target.closest('.mc,button,.chip')) return;
    MM.drag = { x: e.clientX, y: e.clientY, tx: MM.tx, ty: MM.ty, id: e.pointerId }; MM.moved = false;
  });
  v.addEventListener('pointermove', e => {
    const d = MM.drag; if (!d) return;
    const dx = e.clientX - d.x, dy = e.clientY - d.y;
    if (!MM.moved && Math.abs(dx) + Math.abs(dy) > 4) { MM.moved = true; v.setPointerCapture(d.id); v.classList.add('panning'); }
    if (MM.moved) { MM.tx = d.tx + dx; MM.ty = d.ty + dy; applyView(false); }
  });
  const up = () => { MM.drag = null; v.classList.remove('panning'); };
  v.addEventListener('pointerup', up); v.addEventListener('pointercancel', up);
  v.addEventListener('mouseover', e => { const m = e.target.closest('.mm'); codeHover(m ? m.dataset.id : null); });
  v.addEventListener('mouseleave', () => codeHover(null));
}

function mmSelect(sel) {
  let n = sel && byId.get(sel);
  let changed = false;
  if (n && n.f === MM.file && !MM.byNode.has(n.id)) for (let p = n.p; p; p = p.p) if (MM.collapsed.delete(p.id)) changed = true;
  const want = MM.disp === 'names' && n && n.f === MM.file && n.k !== 'module' ? n.id : null;
  if (want !== MM.open) changed = true;
  if (changed) {
    const anchor = MM.byNode.get(want) || MM.byNode.get(MM.open);
    const edge = t => t.side < 0 ? t.x + t.w : t.x;
    const before = anchor && { id: anchor.n.id, x: edge(anchor), y: anchor.y };
    MM.open = want;
    mmLayout();
    const after = before && MM.byNode.get(before.id);
    if (after) { MM.tx += (before.x - edge(after)) * MM.k; MM.ty += (before.y - after.y) * MM.k; applyView(false); }
    const o = MM.byNode.get(MM.open);
    if (o && MM.k < 0.8) zoomAt(edge(o) * MM.k + MM.tx, o.y * MM.k + MM.ty, 0.8, true);
  }
  MM.T.forEach(t => t.el.classList.remove('sel', 'callee', 'caller'));
  const g = $('#mmcalls g'); if (!g) return;
  const t = n && MM.byNode.get(n.id);
  let out = '';
  const link = (a, b, color, mk) => {
    if (a === b) return '';
    const ac = a.x + a.w / 2, bc = b.x + b.w / 2, ay = a.y + a.hh / 2, by = b.y + b.hh / 2;
    if (Math.abs(ac - bc) < (a.w + b.w) / 2) {
      const right = (a.side || 1) > 0, x1 = right ? a.x + a.w : a.x, x2 = right ? b.x + b.w : b.x;
      const X = (right ? Math.max(x1, x2) : Math.min(x1, x2)) + (right ? 1 : -1) * (40 + Math.min(120, Math.abs(by - ay) * 0.12));
      return `<path d="M${x1},${ay}C${X},${ay} ${X},${by} ${x2 + (right ? 4 : -4)},${by}" fill="none" stroke="${color}" stroke-width="2" stroke-dasharray="6 5" marker-end="url(#${mk})"/>`;
    }
    const x1 = bc > ac ? a.x + a.w : a.x, x2 = bc > ac ? b.x - 4 : b.x + b.w + 4, mx = (x1 + x2) / 2;
    return `<path d="M${x1},${ay}C${mx},${ay} ${mx},${by} ${x2},${by}" fill="none" stroke="${color}" stroke-width="2" stroke-dasharray="6 5" marker-end="url(#${mk})"/>`;
  };
  if (t) {
    t.el.classList.add('sel');
    (n.c || []).forEach(id => { const b = MM.byNode.get(id); if (b) { b.el.classList.add('callee'); out += link(t, b, 'var(--accent)', 'ma'); } });
    (n.b || []).forEach(id => { const b = MM.byNode.get(id); if (b) { b.el.classList.add('caller'); out += link(b, t, 'var(--caller)', 'mc'); } });
    const v = $('#mmview'), sx = t.x * MM.k + MM.tx, sy = t.y * MM.k + MM.ty;
    if (t.depth && (sx < 0 || sy < 0 || sx + Math.min(t.w, 300) * MM.k > v.clientWidth || sy + 60 * MM.k > v.clientHeight - 70)) {
      MM.tx = v.clientWidth / 2 - (t.x + t.w / 2) * MM.k; MM.ty = v.clientHeight / 3 - t.y * MM.k; applyView(true);
    } else if (t.n.id === MM.open) {
      const bottom = (t.y + t.h) * MM.k + MM.ty, room = v.clientHeight - 84;
      if (bottom > room) { MM.ty -= Math.min(bottom - room, Math.max(0, sy - 16)); applyView(true); }
    }
  }
  g.innerHTML = out;
}

// ── outline view (stacked boxes) ──
function box(n, total) {
  const blk = !DEFS.has(n.k), kids = (n.ch || []).map(c => box(c, total)).join('');
  const cin = (n.b || []).length, cout = (n.c || []).length;
  const sig = n.k === 'doc' ? n.doc : shortSig(n);
  return `<div class="box k-${n.k}${blk ? ' blk' : ''}" data-id="${esc(n.id)}"><div class="bh"><span class="kp k-${n.k}">${esc(kwOf(n))}</span>${blk ? '' : `<span class="nm">${esc(n.n)}</span>`}<span class="sig">${esc(sig)}</span>
    <span class="sp">${n.s}–${n.e}</span>${cin ? `<span class="cin">←${cin}</span>` : ''}${cout ? `<span class="cout">→${cout}</span>` : ''}</div>
    <div class="track"><i style="left:${(n.s - 1) / total * 100}%;width:${Math.max(0.6, nlines(n) / total * 100)}%"></i></div>${kids ? `<div class="kids">${kids}</div>` : ''}</div>`;
}
function fileView(path) {
  const r = files.get(path).root;
  $('#main').innerHTML = `<div class="ol"><div class="olh"><h2>${esc(base(path))}</h2><span class="kp k-module">${r.e} lines</span><span class="grow"></span>${modeSeg()}</div>
    ${r.err ? `<div class="err">${esc(r.err)}</div>` : ''}
    <div class="flow" id="flow"><svg id="edges"><defs>
      <marker id="ma" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0L8,4L0,8z" fill="var(--accent)"/></marker>
      <marker id="mc" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0L8,4L0,8z" fill="var(--caller)"/></marker></defs><g id="eg"></g></svg>
    ${(r.ch || []).map(c => box(c, r.e)).join('')}</div></div>`;
}
function boxEl(id) { return $(`#flow .box[data-id="${CSS.escape(id)}"]`); }
function edges(sel) {
  const flow = $('#flow'); if (!flow) return;
  const svg = $('#edges'), g = $('#eg');
  svg.setAttribute('width', flow.clientWidth); svg.setAttribute('height', flow.scrollHeight);
  flow.querySelectorAll('.box.sel,.box.callee,.box.caller').forEach(e => e.classList.remove('sel', 'callee', 'caller'));
  g.innerHTML = '';
  const n = sel && byId.get(sel); if (!n) return;
  const fr = flow.getBoundingClientRect();
  const at = id => { const b = boxEl(id); if (!b) return null; const h = b.firstElementChild.getBoundingClientRect(); return { b, x: b.getBoundingClientRect().right - fr.left, y: h.top + h.height / 2 - fr.top }; };
  const me = at(n.id); if (me) me.b.classList.add('sel');
  let paths = '';
  const curve = (a, b, cls, mk) => {
    if (!a || !b || a.b === b.b) return;
    const X = Math.max(a.x, b.x) + 18 + Math.min(80, Math.abs(b.y - a.y) * 0.14);
    paths += `<path d="M${a.x},${a.y} C${X},${a.y} ${X},${b.y} ${b.x + 3},${b.y}" fill="none" stroke="var(--${cls})" stroke-width="1.6" stroke-dasharray="5 4" marker-end="url(#${mk})"/>`;
  };
  (n.c || []).forEach(t => { const p = at(t); if (p) { p.b.classList.add('callee'); curve(me, p, 'accent', 'ma'); } });
  (n.b || []).forEach(t => { const p = at(t); if (p) { p.b.classList.add('caller'); curve(p, me, 'caller', 'mc'); } });
  g.innerHTML = paths;
  if (me) { const r = me.b.getBoundingClientRect(), m = $('#main').getBoundingClientRect(); if (r.top < m.top || r.top > m.bottom - 40) me.b.scrollIntoView({ block: 'center' }); }
}

// ── code pane: the whole file, synced with the map ──
const CODE = { file: null, sel: null, hover: null, rows: [] };
function chips(list) { return list.map(p => `<span class="chip" data-f="${esc(p)}">${esc(base(p))}</span>`).join(''); }
function links(ids, here, cls) {
  return ids.map(id => { const t = byId.get(id); return t ? `<a class="lk ${cls}" data-go="${esc(id)}">${esc(nameOf(t, here))}<small>${t.f === here ? 'L' + t.s : esc(base(t.f))}</small></a>` : ''; }).join('');
}
function codeFile(path) {
  if (CODE.file === path) return;
  CODE.file = path; CODE.sel = null; CODE.hover = null;
  const f = files.get(path), r = f.root, src = $('#src');
  $('#ch').innerHTML = `<span class="pyb">py</span><b title="${esc(path)}">${esc(base(path))}</b><span class="ct">${r.e} lines</span>`;
  const H = hl(path);
  if (!H) { src.innerHTML = '<div class="nosrc">Source not embedded (built with --no-source).</div>'; CODE.rows = []; return; }
  const gc = new Array(H.length + 1).fill('');
  (r.ch || []).forEach((c, i) => { for (let l = c.s; l <= c.e && l <= H.length; l++) gc[l] = PAL[i % PAL.length]; });
  let html = '<div class="srcin">';
  for (let i = 1; i <= H.length; i++) html += `<div class="ln" data-l="${i}"${gc[i] ? ` style="--gc:${gc[i]}"` : ''}><span class="g">${i}</span><span>${H[i - 1] || ' '}</span></div>`;
  src.innerHTML = html + '</div>';
  CODE.rows = [null, ...src.firstElementChild.children];
  src.scrollTop = 0;
}
function paint(range, cls, on, color) {
  if (!range) return;
  for (let l = range[0]; l <= range[1] && l < CODE.rows.length; l++) {
    const el = CODE.rows[l]; if (!el) continue;
    el.classList.toggle(cls, on);
    if (color) el.style.setProperty('--hc', color);
  }
}
function codeSelect(n) {
  paint(CODE.sel, 'hl', false); CODE.sel = null;
  if (!n || n.k === 'module' || !CODE.rows.length) return;
  CODE.sel = [n.s, n.e]; paint(CODE.sel, 'hl', true, colorOf(n));
  const el = CODE.rows[n.s], src = $('#src');
  if (el) src.scrollTo({ top: Math.max(0, el.offsetTop - 40), behavior: 'smooth' });
}
function codeHover(id) {
  if (CODE.hover && CODE.hover.id === id) return;
  if (CODE.hover) paint(CODE.hover.r, 'hv', false);
  CODE.hover = null;
  const n = id && byId.get(id);
  if (n && n.k !== 'module' && n.f === CODE.file) { CODE.hover = { id, r: [n.s, n.e] }; paint(CODE.hover.r, 'hv', true); }
}
function inspector(st) {
  const p = $('#insp');
  if (!st.file) {
    $('#ch').innerHTML = 'About'; $('#src').innerHTML = ''; CODE.file = null; CODE.rows = [];
    const top = [...byId.values()].filter(n => DEFS.has(n.k) && (n.b || []).length).sort((a, b) => b.b.length - a.b.length).slice(0, 14).map(n => n.id);
    p.innerHTML = `<div class="intro"><p>Every file is cut into line-ranged blocks: imports, globals, classes and their methods, functions, the main guard and loose script.</p>
      <p>Open a file to see it as a mind map. The file sits in the middle, and every block branches off as a card holding its own code. The full file stays open in this pane, and clicking a card or a line keeps the two in sync.</p>
      <h5>Most called</h5>${links(top, null, '')}</div>`;
    p.style.maxHeight = 'none';
    return;
  }
  p.style.maxHeight = '';
  const f = files.get(st.file), n = (st.sel && byId.get(st.sel)) || f.root;
  if (n.k === 'module') {
    const s = fstat.get(n.f);
    p.innerHTML = `<div class="ih"><span class="kp k-module">file</span><b>${esc(base(n.f))}</b><span class="rng">${n.e} lines · ${plural(s.cls, 'class').replace('classs', 'classes')} · ${plural(s.fns, 'function')}</span></div>
      ${n.doc ? `<p class="doc">${esc(n.doc)}</p>` : ''}${n.err ? `<p class="err">${esc(n.err)}</p>` : ''}
      ${f.deps.length || f.rdeps.length ? `<div class="rel">${f.deps.length ? `<div><h5>Uses</h5><div class="chips">${chips(f.deps)}</div></div>` : '<div></div>'}${f.rdeps.length ? `<div><h5>Used by</h5><div class="chips">${chips(f.rdeps)}</div></div>` : ''}</div>` : ''}`;
    return;
  }
  const name = pq(n.q);
  p.innerHTML = `<div class="ih"><span class="kp k-${n.k}">${esc(kwOf(n))}</span><b>${esc(name)}</b><span class="rng">L${n.s}–${n.e} · ${nlines(n)} lines</span><button class="btn" id="cp">Copy as context</button></div>
    ${n.sig && DEFS.has(n.k) ? `<div class="sigf">${esc(n.sig)}</div>` : ''}${n.doc ? `<p class="doc">${esc(n.doc)}</p>` : ''}
    ${(n.dec || []).length ? `<div class="xs">${n.dec.map(d => `<code>@${esc(d)}</code>`).join('')}</div>` : ''}
    ${(n.c || []).length || (n.b || []).length ? `<div class="rel"><div><h5>Calls · ${(n.c || []).length}</h5>${links(n.c || [], n.f, '') || '<span class="empty" style="padding:0">none</span>'}</div>
      <div><h5>Called by · ${(n.b || []).length}</h5>${links(n.b || [], n.f, 'in') || '<span class="empty" style="padding:0">none</span>'}</div></div>` : ''}
    ${(n.x || []).length ? `<details class="ext"><summary>External calls · ${n.x.length}</summary><div class="xs">${n.x.map(x => `<code>${esc(x)}</code>`).join('')}</div></details>` : ''}`;
  const cp = $('#cp'), L = srcLines(n.f);
  if (cp && L) cp.onclick = () => {
    const head = [`# ${n.f}::${n.q || '<module>'}  [${n.s}-${n.e}]`];
    if (n.sig) head.push('# sig: ' + n.sig);
    if ((n.c || []).length) head.push('# calls: ' + n.c.map(id => nameOf(byId.get(id), n.f)).join(', '));
    if ((n.b || []).length) head.push('# called by: ' + n.b.map(id => nameOf(byId.get(id), n.f)).join(', '));
    const text = head.join('\n') + '\n' + L.slice(n.s - 1, n.e).join('\n');
    const done = () => { cp.textContent = 'Copied'; setTimeout(() => cp.textContent = 'Copy as context', 1200); };
    (navigator.clipboard ? navigator.clipboard.writeText(text) : Promise.reject()).then(done, () => {
      const t = document.createElement('textarea'); t.value = text; document.body.appendChild(t); t.select();
      try { document.execCommand('copy'); done(); } catch (e) {} t.remove();
    });
  };
}

// ── routing ──
let lastKey = undefined;
function render() {
  const st = state();
  if (!location.hash && D.start && files.has(D.start)) st.file = D.start;
  if (st.file && !files.has(st.file)) st.file = null;
  if (st.sel && byId.has(st.sel) && !st.file) st.file = byId.get(st.sel).f;
  crumbs(st); explorer(st);
  const map = !!st.file && MODE === 'map';
  document.body.classList.toggle('mapmode', map);
  const key = st.file ? st.file + '|' + MODE + '|' + MM.disp : null;
  if (!st.file) { if (lastKey !== null) overview(); lastKey = null; }
  else if (key !== lastKey) { map ? mapView(st.file) : fileView(st.file); lastKey = key; }
  if (st.file) codeFile(st.file);
  inspector(st);
  const n = st.sel && byId.get(st.sel);
  codeSelect(n);
  if (map) mmSelect(st.sel); else if (st.file) requestAnimationFrame(() => edges(st.sel));
}

document.addEventListener('click', e => {
  if (MM.moved) { MM.moved = false; return; }
  const tg = e.target.closest('[data-toggle]');
  if (tg) { const p = tg.dataset.toggle, on = document.body.classList.toggle('no' + p); store.set('epy.hide.' + p, on ? '1' : '0'); return; }
  if (e.target.closest('[data-theme-toggle]')) {
    const dark = THEME === 'dark' || (THEME === 'auto' && matchMedia('(prefers-color-scheme: dark)').matches);
    THEME = dark ? 'light' : 'dark'; store.set('epy.theme', THEME); applyTheme(); return;
  }
  if (e.target.closest('[data-home]')) { $('#q').value = ''; location.hash = ''; render(); return; }
  const dr = e.target.closest('[data-dir]');
  if (dr) {
    const p = dr.dataset.dir;
    if (dr.closest('.crumbs')) { OPEN.add(p); document.body.classList.remove('noside'); }
    else if (OPEN.has(p)) OPEN.delete(p); else OPEN.add(p);
    saveOpen(); explorer(state()); return;
  }
  const kn = e.target.closest('[data-knob]');
  if (kn) { const id = kn.dataset.knob; MM.collapsed.has(id) ? MM.collapsed.delete(id) : MM.collapsed.add(id); mmLayout(); mmSelect(state().sel); return; }
  const md = e.target.closest('[data-mode]'); if (md) { MODE = md.dataset.mode; store.set('epy.mode', MODE); render(); return; }
  const dp = e.target.closest('[data-disp]'); if (dp) { MM.disp = dp.dataset.disp; store.set('epy.disp', MM.disp); render(); return; }
  const ac = e.target.closest('[data-act]');
  if (ac) {
    const a = ac.dataset.act, v = $('#mmview');
    if (a === 'tree-collapse') { OPEN.clear(); saveOpen(); $('#tree').innerHTML = treeHTML(TREE, 0, state().file); }
    else if (a === 'fit') mmFit(true);
    else if (a === 'zin' || a === 'zout') zoomAt(v.clientWidth / 2, v.clientHeight / 2, MM.k * (a === 'zin' ? 1.3 : 1 / 1.3), true);
    else {
      MM.collapsed = new Set();
      if (a === 'collapse') for (const n of byId.values()) if (n.f === MM.file && n.k !== 'module' && (n.ch || []).length) MM.collapsed.add(n.id);
      mmLayout(); mmSelect(state().sel); mmFit(false);
    }
    return;
  }
  const g = e.target.closest('[data-go]'); if (g) { const n = byId.get(g.dataset.go); if (n) go(n.f, n.id); return; }
  const f = e.target.closest('[data-f]'); if (f) { $('#q').value = ''; go(f.dataset.f); return; }
  const mm = e.target.closest('.mm');
  if (mm) { if (e.target.closest('.mc') && !window.getSelection().isCollapsed) return; const n = byId.get(mm.dataset.id); go(n.f, n.k === 'module' ? null : n.id); return; }
  const b = e.target.closest('.box'); if (b) { const n = byId.get(b.dataset.id); go(n.f, n.id); return; }
  const ln = e.target.closest('.ln');
  if (ln && window.getSelection().isCollapsed) { const n = innermost(CODE.file, +ln.dataset.l); go(n.f, n.k === 'module' ? null : n.id); }
});
$('#q').addEventListener('input', () => explorer(state()));
document.addEventListener('keydown', e => {
  const typing = document.activeElement === $('#q');
  if (e.key === '/' && !typing) { e.preventDefault(); document.body.classList.remove('noside'); $('#q').focus(); }
  else if (e.key === 'Escape') { if ($('#q').value) { $('#q').value = ''; explorer(state()); } else { const st = state(); if (st.sel) go(st.file); } }
  else if (e.key === 'f' && !typing && document.body.classList.contains('mapmode')) mmFit(true);
});
window.addEventListener('hashchange', render);
window.addEventListener('resize', () => { if (!document.body.classList.contains('mapmode')) edges(state().sel); });
render();
</script></body></html>
"""


def main(argv=None):
    ap = argparse.ArgumentParser(prog="epy", description="extended python graph — block map of a Python codebase")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("path", type=Path, help="a .py file or a directory")
        p.add_argument("--exclude", action="append", default=[], metavar="GLOB",
                       help="skip files matching this glob (relative path), repeatable")
        return p

    m = common(sub.add_parser("map", help="print the block map (.epy text)"))
    m.add_argument("-o", "--out", type=Path)
    m.add_argument("--depth", type=int, default=99, help="nesting depth to print")
    m.add_argument("--no-calls", action="store_true", help="hide → call lists")
    m.add_argument("--external", action="store_true", help="also list unresolved external calls")

    s = common(sub.add_parser("show", help="print one box's code with its calls/callers"))
    s.add_argument("target", help="file.py::Class.method | Class.method | file.py:LINE | file.py")

    h = common(sub.add_parser("html", help="write the interactive flowchart"))
    h.add_argument("-o", "--out", type=Path, default=Path("epy.html"))
    h.add_argument("--no-source", action="store_true", help="don't embed source code")

    v = common(sub.add_parser("view", help="build the mind map and open it in the browser"))
    v.add_argument("--root", type=Path, help="project root for cross-file links (default: cwd if PATH is inside it)")
    v.add_argument("-o", "--out", type=Path, help="where to write the html (default: temp dir)")

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
            print(f"wrote {a.out}  ({len(text.splitlines())} lines, {len(text):,} chars)")
        else:
            print(text)
    elif a.cmd == "show":
        hits = proj.find(a.target)
        if not hits:
            sys.exit(f"no box matches {a.target!r}")
        if len(hits) > 1:
            print(f"{len(hits)} boxes match {a.target!r}; be more specific:", file=sys.stderr)
            for n in hits[:40]:
                print(f"  {n.file}::{n.qual}  [{n.start}-{n.end}]", file=sys.stderr)
            sys.exit(1)
        print(render_show(proj, hits[0]))
    elif a.cmd == "html":
        a.out.write_text(render_html(proj, not a.no_source), encoding="utf-8")
        st = proj.stats()
        print(f"wrote {a.out}  ({st['files']} files, {st['lines']:,} lines, {st['edges']} edges)")
    elif a.cmd == "json":
        a.out.write_text(json.dumps(proj.to_dict(not a.no_source), indent=1), encoding="utf-8")
        print(f"wrote {a.out}")


if __name__ == "__main__":
    main()
