"""Certificates of non-flat-foldability, and their verification.

A certificate is a list of linear equations over F2, each one a constraint
that every flat-folded state satisfies:

* a taco--tortilla or taco--taco **row** of the pattern;
* an **assignment fact**: the crease ``e_ij`` carries the label given in the
  file, which by Eq. (1) of the paper fixes its layer variable,
  ``x_ij = s + [p_i = -1]`` with ``s = 0`` for a mountain and ``1`` for a
  valley (``i < j``).

The left-hand sides cancel and the constants add up to one, so the equations
have no common solution: no flat-folded state exists (Corollary 4 of the
paper).  Checking this needs nothing but additions modulo two
(:meth:`Certificate.holds`); checking that every equation really is a
constraint of the pattern is done by :func:`verify` against the file.

The JSON form identifies facets, creases and vertices by points in the
coordinates of the file, so that it can be checked independently of the
numbering used by this program.
"""

from __future__ import annotations

import hashlib
import json
import math
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from .rows import Row, canonical

__all__ = ["Certificate", "Item", "verify", "VerifyResult", "FORMAT"]

FORMAT = "linfold-certificate"
VERSION = 1


@dataclass
class Item:
    """One equation of a certificate."""

    kind: str                                   #: 'TT', 'TC' or 'assignment'
    row: Optional[Row] = None
    crease: Optional[int] = None                #: for an assignment fact
    label: Optional[str] = None                 #: 'M' or 'V'
    facets: Optional[Tuple[int, int]] = None    #: the crease's facets, i < j
    side: Optional[int] = None                  #: p_i of the first facet

    def equation(self) -> Tuple[Tuple[Tuple[int, int], ...], int]:
        if self.kind == "assignment":
            s = 0 if self.label == "M" else 1
            return (self.facets,), s ^ int(self.side < 0)
        return self.row.equation()


@dataclass
class Group:
    """Rows that add up to one relation at one vertex (local certificates)."""

    vertex: int
    creases: Tuple[int, ...]
    parity: int                                 #: number of valleys mod 2
    items: List[int]


@dataclass
class Certificate:
    claim: str                                  #: 'pattern' or 'assignment'
    level: str                                  #: 'local' or 'global'
    items: List[Item]
    groups: List[Group] = field(default_factory=list)

    def total(self):
        """The F2-sum of all the equations: ``(pairs, const)``."""
        terms, const = [], 0
        for it in self.items:
            pairs, c = it.equation()
            terms.extend(pairs)
            const ^= c
        pairs, c = canonical(terms)
        return pairs, const ^ c

    def holds(self) -> bool:
        """Do the left-hand sides cancel, with constants adding up to one?"""
        pairs, const = self.total()
        return not pairs and const == 1

    @property
    def rows(self) -> List[Row]:
        return [it.row for it in self.items if it.row is not None]

    # ------------------------------------------------------------ JSON
    def to_json(self, cp, source: Optional[str] = None) -> dict:
        """A self-describing dictionary, with geometry in file coordinates."""
        facets, creases, vertices = set(), set(), set()
        for it in self.items:
            if it.row is not None:
                for a, b in it.row.terms:
                    facets.update((a, b))
                creases.update(it.row.creases)
                if it.row.vertex is not None:
                    vertices.add(it.row.vertex)
            else:
                creases.add(it.crease)
                facets.update(it.facets)
        for g in self.groups:
            vertices.add(g.vertex)
            creases.update(g.creases)
        for c in list(creases):
            facets.update(cp.creases[c].facets)

        def pt(p):
            x, y = cp.original(p)
            return [round(x, 12), round(y, 12)]

        def eq(it):
            pairs, const = it.equation()
            return {"pairs": [list(p) for p in pairs], "rhs": const}

        items = []
        for it in self.items:
            if it.kind == "assignment":
                items.append({"kind": "assignment", "crease": it.crease,
                              "label": it.label, "side": it.side,
                              "equation": eq(it)})
            else:
                r = it.row
                d = {"kind": r.kind, "creases": list(r.creases),
                     "terms": [list(t) for t in r.terms], "equation": eq(it)}
                if r.tortilla is not None:
                    d["tortilla"] = r.tortilla
                if r.vertex is not None:
                    d["vertex"] = r.vertex
                items.append(d)
        doc = {
            "format": FORMAT,
            "version": VERSION,
            "claim": self.claim,
            "level": self.level,
            "statement": ("The equations below hold in every flat-folded state of "
                          + ("the pattern" if self.claim == "pattern" else
                             "the pattern with the given mountain-valley labels")
                          + ". Their left-hand sides cancel over F2 and their "
                            "constants add up to 1, so no flat-folded state exists."),
            "pattern": {"name": cp.name},
            "facets": {str(f): {"point": pt(cp.facet_point(f))} for f in sorted(facets)},
            "creases": {str(c): {"facets": list(cp.creases[c].facets),
                                 "midpoint": pt(_mid(cp.creases[c].segment)),
                                 "label": cp.creases[c].assignment}
                        for c in sorted(creases)},
            "vertices": {str(v): {"point": pt(cp.vertices[v].point)}
                         for v in sorted(vertices)},
            "items": items,
            "relations": [{"vertex": g.vertex, "creases": list(g.creases),
                           "valley_parity": g.parity, "items": g.items}
                          for g in self.groups],
            "sum": {"pairs": [], "rhs": 1},
        }
        if source:
            with open(source, "rb") as fh:
                doc["pattern"]["sha256"] = hashlib.sha256(fh.read()).hexdigest()
            doc["pattern"]["file"] = source.replace("\\", "/").rsplit("/", 1)[-1]
        return doc

    @staticmethod
    def from_json(doc: dict) -> "Certificate":
        if doc.get("format") != FORMAT:
            raise ValueError("not a linfold certificate")
        items = []
        for d in doc["items"]:
            if d["kind"] == "assignment":
                pairs = d["equation"]["pairs"]
                items.append(Item("assignment", crease=d["crease"], label=d["label"],
                                  facets=tuple(pairs[0]), side=d["side"]))
            else:
                r = Row(d["kind"], tuple(d["creases"]), d.get("tortilla"),
                        tuple(tuple(t) for t in d["terms"]), d.get("vertex"))
                items.append(Item(d["kind"], row=r))
        groups = [Group(g["vertex"], tuple(g["creases"]), g["valley_parity"], g["items"])
                  for g in doc.get("relations", [])]
        return Certificate(doc["claim"], doc["level"], items, groups)


def _mid(seg):
    (x0, y0), (x1, y1) = seg
    return ((x0 + x1) / 2, (y0 + y1) / 2)


# ------------------------------------------------------------------ verify
@dataclass
class VerifyResult:
    algebra: bool                    #: the equations add up to 0 = 1
    geometry: Optional[bool]         #: every equation is a constraint of the pattern
    messages: List[str]

    @property
    def ok(self) -> bool:
        return self.algebra and self.geometry is not False


def verify(doc: dict, cp=None) -> VerifyResult:
    """Check a certificate (as loaded from JSON).

    Without a pattern, only the algebra is checked: the stated equations add
    up to ``0 = 1``, and each one is what its row says (the terms of a TT or
    TC row, brought to canonical form).  With a pattern
    (:class:`linfold.pattern.CreasePattern`), every facet, crease and vertex
    is located by its point, every row is recomputed from the geometry and
    looked up, and every assignment fact is compared with the file.
    """
    msgs: List[str] = []
    cert = Certificate.from_json(doc)
    ok_alg = True
    for i, (it, d) in enumerate(zip(cert.items, doc["items"])):
        pairs, const = it.equation()
        stated = (tuple(tuple(p) for p in d["equation"]["pairs"]), d["equation"]["rhs"])
        if (pairs, const) != stated:
            ok_alg = False
            msgs.append(f"item {i}: the stated equation is not the canonical form "
                        "of its terms")
    if not cert.holds():
        ok_alg = False
        pairs, const = cert.total()
        msgs.append(f"the equations add up to {len(pairs)} surviving variable(s) "
                    f"= {const}, not 0 = 1")
    if ok_alg:
        msgs.append(f"algebra: the {len(cert.items)} equations add up to 0 = 1")
    if cp is None:
        return VerifyResult(ok_alg, None, msgs)

    ok_geo = True
    fmap, cmap, vmap = _locate(doc, cp, msgs)
    if fmap is None:
        return VerifyResult(ok_alg, False, msgs)
    local: Dict[int, set] = {}
    global_rows = None
    flips = set()
    for i, it in enumerate(cert.items):
        if it.kind == "assignment":
            c = cmap[it.crease]
            crease = cp.creases[c]
            a, b = (fmap[it.facets[0]], fmap[it.facets[1]])
            if {a, b} != set(crease.facets):
                ok_geo = False
                msgs.append(f"item {i}: crease {it.crease} does not separate the "
                            "stated facets")
            elif crease.assignment != it.label:
                ok_geo = False
                msgs.append(f"item {i}: the file labels this crease "
                            f"{crease.assignment!r}, not {it.label!r}")
            # the sides p_i are fixed up to turning the whole sheet over, which
            # changes the constants of an even number of facts and leaves the
            # sum unchanged; they must agree with a two-colouring up to that
            flips.add(it.side * cp.side[a])
            continue
        r = it.row
        key = (r.kind, tuple(sorted(cmap[c] for c in r.creases)),
               fmap[r.tortilla] if r.tortilla is not None else None,
               canonical([(fmap[a], fmap[b]) for a, b in r.terms]))
        found = False
        if r.vertex is not None and r.vertex in vmap:
            v = vmap[r.vertex]
            if v not in local:
                pv = cp.vertices[v]
                local[v] = {_key(x) for x in cp.local_rows(pv)} if pv.vertex else set()
            found = key in local[v]
        if not found:
            if global_rows is None:
                global_rows = {_key(x) for x in cp.folding.rows}
            found = key in global_rows
        if not found:
            ok_geo = False
            msgs.append(f"item {i}: {r.kind} row not found in the pattern")
    if len(flips) > 1:
        ok_geo = False
        msgs.append("the sides p_i of the assignment facts do not come from one "
                    "two-colouring of the facets")
    if ok_geo:
        msgs.append("geometry: every row is a constraint of the pattern, and every "
                    "assignment fact agrees with the file")
    return VerifyResult(ok_alg, ok_geo, msgs)


def _key(r: Row):
    return (r.kind, tuple(sorted(r.creases)), r.tortilla, canonical(r.terms))


def _locate(doc, cp, msgs):
    """Map the certificate's facets, creases and vertices to those of ``cp``."""
    unit = lambda p: ((p[0] - cp.graph.centre[0]) * cp.graph.scale,   # noqa: E731
                      (p[1] - cp.graph.centre[1]) * cp.graph.scale)
    from . import geometry as G
    fmap, cmap, vmap = {}, {}, {}
    polys = cp.facet_polygons
    for k, d in doc["facets"].items():
        p = unit(d["point"])
        hits = [f for f, P in enumerate(polys) if len(P) >= 3 and _inside(p, P)]
        if len(hits) != 1:
            msgs.append(f"facet {k}: its point lies in {len(hits)} facets of the pattern")
            return None, None, None
        fmap[int(k)] = hits[0]
    for k, d in doc["creases"].items():
        want = frozenset(fmap[f] for f in d["facets"])
        c = next((c.id for c in cp.creases if frozenset(c.facets) == want), None)
        if c is None:
            msgs.append(f"crease {k}: no crease separates its two facets")
            return None, None, None
        cmap[int(k)] = c
    for k, d in doc["vertices"].items():
        p = unit(d["point"])
        best = min(cp.vertices, key=lambda v: math.dist(v.point, p), default=None)
        if best is None or math.dist(best.point, p) > 1e-6:
            msgs.append(f"vertex {k}: no interior vertex at its point")
            return None, None, None
        vmap[int(k)] = best.id
    return fmap, cmap, vmap


def _inside(p, poly) -> bool:
    c = False
    n = len(poly)
    for i in range(n):
        (xa, ya), (xb, yb) = poly[i], poly[(i + 1) % n]
        if (ya > p[1]) != (yb > p[1]):
            if p[0] < xa + (p[1] - ya) * (xb - xa) / (yb - ya):
                c = not c
    return c


def load_certificate(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)
