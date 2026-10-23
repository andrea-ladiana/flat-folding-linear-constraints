"""From a drawing to a planar subdivision.

A ``.cp``, ``.opx`` or ``.svg`` file is a set of segments: nothing guarantees
that two creases meet at a recorded vertex rather than crossing each other,
and nothing gives the faces.  :func:`planarise`

1. brings the drawing to unit size (all tolerances are then absolute);
2. splits every segment at its intersections with the others (crossings,
   T-junctions, collinear overlaps) and welds points closer than ``1e-7``;
3. removes dangling edges, recording the folded ones, since a crease that
   stops inside the sheet makes the pattern unfoldable;
4. recovers the faces by the half-edge walk.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from .formats import FOLDS, RawPattern

__all__ = ["PlanarGraph", "PlanarityError", "planarise", "WELD_TOL"]

Point = Tuple[float, float]

#: points closer than this (on the unit-size drawing) are one point
WELD_TOL = 1e-7


class PlanarityError(ValueError):
    """The drawing cannot be resolved into a planar subdivision."""


@dataclass
class PlanarGraph:
    """A planar subdivision of the sheet, on the unit-size drawing."""

    vertices: List[Point]
    edges: List[Tuple[int, int]]                 # (u, v) with u < v
    assignments: List[str]
    faces: List[List[int]]                       # counterclockwise vertex cycles
    left: Dict[Tuple[int, int], int]             # half-edge -> face on its left (-1 outer)
    outer: Set[int]                              # vertices on the boundary of the sheet
    scale: float = 1.0                           # unit coordinates = (xy - centre) * scale
    centre: Point = (0.0, 0.0)
    notes: List[str] = field(default_factory=list)
    dangling_creases: List[Point] = field(default_factory=list)

    def to_original(self, p: Point) -> Point:
        return (p[0] / self.scale + self.centre[0], p[1] / self.scale + self.centre[1])


# ----------------------------------------------------------------- welding
class _Welder:
    def __init__(self, tol: float):
        self.tol = tol
        self.pts: List[Point] = []
        self.grid: Dict[Tuple[int, int], List[int]] = {}

    def __call__(self, p: Point) -> int:
        kx, ky = round(p[0] / self.tol), round(p[1] / self.tol)
        best, bd = None, self.tol
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for i in self.grid.get((kx + dx, ky + dy), ()):
                    d = math.dist(self.pts[i], p)
                    if d <= bd:
                        best, bd = i, d
        if best is not None:
            return best
        self.pts.append((float(p[0]), float(p[1])))
        self.grid.setdefault((kx, ky), []).append(len(self.pts) - 1)
        return len(self.pts) - 1


# ---------------------------------------------------------------- splitting
def _cuts(segs: List[Tuple[Point, Point]], tol: float) -> List[List[float]]:
    """For every segment, the parameters (as distances) of its cut points."""
    n = len(segs)
    cuts: List[List[float]] = [[] for _ in range(n)]
    boxes = []
    for p, q in segs:
        boxes.append((min(p[0], q[0]) - tol, max(p[0], q[0]) + tol,
                      min(p[1], q[1]) - tol, max(p[1], q[1]) + tol))
    order = sorted(range(n), key=lambda i: boxes[i][0])
    active: List[int] = []
    for i in order:
        x0 = boxes[i][0]
        active = [j for j in active if boxes[j][1] >= x0]
        for j in active:
            if boxes[j][3] < boxes[i][2] or boxes[i][3] < boxes[j][2]:
                continue
            for pt in _meet(segs[i], segs[j], tol):
                cuts[i].append(_param(segs[i], pt))
                cuts[j].append(_param(segs[j], pt))
        active.append(i)
    return cuts


def _param(seg, pt) -> float:
    (px, py), (qx, qy) = seg
    L = math.hypot(qx - px, qy - py)
    return ((pt[0] - px) * (qx - px) + (pt[1] - py) * (qy - py)) / L


def _on_segment(seg, pt, tol) -> bool:
    (px, py), (qx, qy) = seg
    dx, dy = qx - px, qy - py
    L = math.hypot(dx, dy)
    t = ((pt[0] - px) * dx + (pt[1] - py) * dy) / L
    if t < -tol or t > L + tol:
        return False
    return abs(dx * (pt[1] - py) - dy * (pt[0] - px)) / L <= tol


def _meet(s1, s2, tol) -> List[Point]:
    """The points where two segments meet (two for a collinear overlap)."""
    (p, q), (r, s) = s1, s2
    d1 = (q[0] - p[0], q[1] - p[1])
    d2 = (s[0] - r[0], s[1] - r[1])
    L1, L2 = math.hypot(*d1), math.hypot(*d2)
    den = d1[0] * d2[1] - d1[1] * d2[0]
    out = []
    if abs(den) <= 1e-12 * L1 * L2:                # parallel
        for pt in (r, s):
            if _on_segment(s1, pt, tol):
                out.append(pt)
        for pt in (p, q):
            if _on_segment(s2, pt, tol):
                out.append(pt)
        return out
    w = (r[0] - p[0], r[1] - p[1])
    t = (w[0] * d2[1] - w[1] * d2[0]) / den
    u = (w[0] * d1[1] - w[1] * d1[0]) / den
    if -tol / L1 <= t <= 1 + tol / L1 and -tol / L2 <= u <= 1 + tol / L2:
        out.append((p[0] + t * d1[0], p[1] + t * d1[1]))
    return out


# ---------------------------------------------------------------- planarise
def planarise(raw: RawPattern) -> PlanarGraph:
    """Resolve a drawing into a planar subdivision of the unit-size sheet."""
    if not raw.vertices or not raw.edges:
        raise PlanarityError("the pattern is empty")
    x0, y0, x1, y1 = raw.bbox()
    span = max(x1 - x0, y1 - y0)
    if span <= 0:
        raise PlanarityError("the pattern has no extent")
    scale = 1.0 / span
    centre = ((x0 + x1) / 2, (y0 + y1) / 2)
    unit = [((x - centre[0]) * scale, (y - centre[1]) * scale) for x, y in raw.vertices]

    segs, assign = [], []
    for (u, v), a in zip(raw.edges, raw.assignments):
        p, q = unit[u], unit[v]
        if math.dist(p, q) > WELD_TOL:
            segs.append((p, q))
            assign.append(a)
    cuts = _cuts(segs, WELD_TOL)

    weld = _Welder(WELD_TOL)
    rank = {"U": 0, "F": 1, "B": 2, "M": 3, "V": 3}
    emap: Dict[Tuple[int, int], str] = {}
    conflicts = 0
    for (p, q), a, cs in zip(segs, assign, cuts):
        L = math.dist(p, q)
        ts = sorted({0.0, L, *[t for t in cs if WELD_TOL < t < L - WELD_TOL]})
        ux, uy = (q[0] - p[0]) / L, (q[1] - p[1]) / L
        ids = [weld((p[0] + t * ux, p[1] + t * uy)) for t in ts]
        for i, j in zip(ids, ids[1:]):
            if i == j:
                continue
            e = (min(i, j), max(i, j))
            old = emap.get(e)
            if old is None:
                emap[e] = a
            else:
                if {old, a} == {"M", "V"}:
                    conflicts += 1
                if rank[a] > rank[old]:
                    emap[e] = a
    pts = weld.pts
    notes = []
    if conflicts or raw.meta.get("duplicate_conflicts"):
        notes.append("some segments are drawn twice, once as a mountain and once "
                     "as a valley; the first label was kept")

    # dangling edges: a vertex of degree one bounds no face
    edges = dict(emap)
    deg: Dict[int, int] = {}
    inc: Dict[int, List[Tuple[int, int]]] = {}
    for e in edges:
        for w in e:
            deg[w] = deg.get(w, 0) + 1
            inc.setdefault(w, []).append(e)
    stack = [w for w, d in deg.items() if d == 1]
    dangling: List[Point] = []
    pruned = 0
    while stack:
        w = stack.pop()
        if deg.get(w) != 1:
            continue
        for e in inc[w]:
            if e in edges:
                if edges[e] in "MV":
                    dangling.append(pts[w])
                del edges[e]
                pruned += 1
                deg[w] -= 1
                o = e[0] if e[1] == w else e[1]
                deg[o] -= 1
                if deg[o] == 1:
                    stack.append(o)
                break
    if pruned:
        notes.append(f"{pruned} dangling edge(s) removed")

    elist = sorted(edges)
    alist = [edges[e] for e in elist]
    faces, left, outer_cycles = _faces(pts, elist)
    if not faces:
        raise PlanarityError("the drawing encloses no region")
    if len(outer_cycles) != 1:
        raise PlanarityError(
            f"the drawing has {len(outer_cycles)} connected components; draw the "
            "boundary of the sheet so that every crease meets it or another crease")
    outer = set(outer_cycles[0])
    ring = [pts[i] for i in outer_cycles[0]]
    inside, beyond = [], 0
    for p in dangling:
        if _strictly_inside(p, ring):
            inside.append((p[0] / scale + centre[0], p[1] / scale + centre[1]))
        else:
            beyond += 1
    if beyond:
        notes.append(f"{beyond} crease piece(s) outside the sheet removed")
    return PlanarGraph(pts, elist, alist, faces, left, outer, scale, centre,
                       notes, inside)


def _strictly_inside(p: Point, ring: List[Point], tol: float = 10 * WELD_TOL) -> bool:
    """Is ``p`` inside the polygon ``ring``, farther than ``tol`` from it?"""
    n = len(ring)
    for i in range(n):
        a, b = ring[i], ring[(i + 1) % n]
        dx, dy = b[0] - a[0], b[1] - a[1]
        L2 = dx * dx + dy * dy
        t = 0.0 if L2 == 0 else max(0.0, min(1.0, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / L2))
        if math.dist(p, (a[0] + t * dx, a[1] + t * dy)) <= tol:
            return False
    c = False
    for i in range(n):
        (xa, ya), (xb, yb) = ring[i], ring[(i + 1) % n]
        if (ya > p[1]) != (yb > p[1]):
            if p[0] < xa + (p[1] - ya) * (xb - xa) / (yb - ya):
                c = not c
    return c


def _faces(pts: List[Point], edges: List[Tuple[int, int]]):
    """The half-edge walk: bounded faces counterclockwise, and outer cycles."""
    nbr: Dict[int, List[int]] = {}
    for u, v in edges:
        nbr.setdefault(u, []).append(v)
        nbr.setdefault(v, []).append(u)
    order, rank = {}, {}
    for w, ws in nbr.items():
        ring = sorted(ws, key=lambda z: math.atan2(pts[z][1] - pts[w][1],
                                                   pts[z][0] - pts[w][0]))
        order[w] = ring
        rank[w] = {z: i for i, z in enumerate(ring)}

    def nxt(u, v):
        ring = order[v]
        return ring[(rank[v][u] - 1) % len(ring)]

    left: Dict[Tuple[int, int], int] = {}
    faces: List[List[int]] = []
    outer_cycles: List[List[int]] = []
    seen = set()
    halves = [(u, v) for u, v in edges] + [(v, u) for u, v in edges]
    for h in halves:
        if h in seen:
            continue
        cyc, hs = [], []
        u, v = h
        while (u, v) not in seen:
            seen.add((u, v))
            cyc.append(u)
            hs.append((u, v))
            u, v = v, nxt(u, v)
        a = 0.0
        for i in range(len(cyc)):
            xa, ya = pts[cyc[i]]
            xb, yb = pts[cyc[(i + 1) % len(cyc)]]
            a += xa * yb - xb * ya
        if a > 1e-14:
            fid = len(faces)
            faces.append(cyc)
            for e in hs:
                left[e] = fid
        else:
            outer_cycles.append(cyc)
            for e in hs:
                left[e] = -1
    return faces, left, outer_cycles
