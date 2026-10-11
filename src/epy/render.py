from __future__ import annotations

import html
import json
import re
from pathlib import Path, PurePosixPath

from epy.node import Node
from epy.project import Project
from epy.constants import FUNC


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
