from __future__ import annotations

import argparse

import json
import sys
import tempfile
import webbrowser
from pathlib import Path

from epy.project import Project
from epy.render import render_html, render_map, render_show


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
