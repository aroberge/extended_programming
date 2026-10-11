from __future__ import annotations


import ast
from pathlib import PurePosixPath

from epy.node import Node


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
