from __future__ import annotations
from dataclasses import dataclass, field

from typing import Optional


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
    children: list[Node] = field(default_factory=list)
    parent: Optional[Node] = field(default=None, repr=False)
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
