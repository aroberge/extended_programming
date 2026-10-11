from __future__ import annotations


import fnmatch
import re
from datetime import datetime
from pathlib import Path, PurePosixPath

from epy.file_graph import FileGraph
from epy.node import Node
from epy.constants import SKIP_DIRS, FUNC, DEFS, MAX_DEPTH


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
                bt = self.resolve(b, node.parent, depth + 1)  # type: ignore
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
            s = s.parent  # type: ignore
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
            s = s.parent  # type: ignore
        return None

    @staticmethod
    def enclosing_class(scope: Node) -> Node | None:
        s = scope
        while s is not None and s.kind != "class":
            s = s.parent  # type: ignore
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
