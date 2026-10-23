"""Plane geometry for folded crease patterns, in pure Python.

The pattern is first brought to unit size (:mod:`linfold.planar`), so the
tolerances below are absolute.  The two predicates that decide the rows,
whether a segment runs through the interior of a convex polygon and whether
two segments overlap along a common line, are computed with explicit line
arithmetic: a segment lying along an edge of a polygon must count as *not*
crossing its interior, and a generic intersection routine gets exactly that
case wrong.
"""

from __future__ import annotations

import math
from typing import List, Optional, Sequence, Tuple

__all__ = ["Iso", "AREA_TOL", "LEN_TOL", "COLLINEAR_TOL", "area2", "ccw",
           "clip_convex", "intersection_area", "inside_length",
           "collinear_overlap", "is_convex", "simplify", "bbox"]

Point = Tuple[float, float]
Polygon = List[Point]

#: an overlap of positive area, on a pattern of unit size
AREA_TOL = 1e-9
#: a segment of positive length
LEN_TOL = 1e-6
#: distance below which a point lies on a line.  It must exceed the welding
#: tolerance of :mod:`linfold.planar` (1e-7), which moves points by up to that
#: much: two crease images that coincide would otherwise drift apart.
COLLINEAR_TOL = 1e-6


def area2(poly: Sequence[Point]) -> float:
    """Twice the signed area (positive for counterclockwise)."""
    s = 0.0
    n = len(poly)
    for i in range(n):
        x0, y0 = poly[i]
        x1, y1 = poly[(i + 1) % n]
        s += x0 * y1 - x1 * y0
    return s


def ccw(poly: Sequence[Point]) -> Polygon:
    poly = list(poly)
    return poly if area2(poly) >= 0 else poly[::-1]


def bbox(poly: Sequence[Point]) -> Tuple[float, float, float, float]:
    xs = [p[0] for p in poly]
    ys = [p[1] for p in poly]
    return min(xs), min(ys), max(xs), max(ys)


def _cross(o: Point, a: Point, b: Point) -> float:
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def clip_convex(subject: Sequence[Point], clipper: Sequence[Point]) -> Polygon:
    """Sutherland--Hodgman: the part of ``subject`` inside the convex,
    counterclockwise polygon ``clipper``."""
    out = list(subject)
    n = len(clipper)
    for i in range(n):
        if not out:
            break
        a, b = clipper[i], clipper[(i + 1) % n]
        inp, out = out, []
        m = len(inp)
        for j in range(m):
            p, q = inp[j], inp[(j + 1) % m]
            sp, sq = _cross(a, b, p), _cross(a, b, q)
            if sp >= 0:
                out.append(p)
            if (sp >= 0) != (sq >= 0):
                t = sp / (sp - sq)
                out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def intersection_area(polys: Sequence[Sequence[Point]]) -> float:
    """Area of the intersection of convex counterclockwise polygons."""
    cur = list(polys[0])
    for P in polys[1:]:
        cur = clip_convex(cur, P)
        if len(cur) < 3:
            return 0.0
    return abs(area2(cur)) / 2.0


def _dist_to_line(p: Point, q: Point, r: Point) -> float:
    dx, dy = q[0] - p[0], q[1] - p[1]
    L = math.hypot(dx, dy)
    if L == 0:
        return math.hypot(r[0] - p[0], r[1] - p[1])
    return abs(dx * (r[1] - p[1]) - dy * (r[0] - p[0])) / L


def inside_length(p: Point, q: Point, poly: Sequence[Point],
                  tol: float = COLLINEAR_TOL) -> float:
    """Length of the part of segment ``pq`` in the interior of a convex,
    counterclockwise polygon; zero when ``pq`` runs along an edge line."""
    n = len(poly)
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        if _dist_to_line(p, q, a) < tol and _dist_to_line(p, q, b) < tol:
            return 0.0
    dx, dy = q[0] - p[0], q[1] - p[1]
    L = math.hypot(dx, dy)
    if L == 0:
        return 0.0
    ux, uy = dx / L, dy / L
    t0, t1 = 0.0, L
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        ex, ey = b[0] - a[0], b[1] - a[1]
        el = math.hypot(ex, ey)
        if el == 0:
            continue
        nx, ny = -ey / el, ex / el                  # inward normal (ccw)
        dist_p = nx * (p[0] - a[0]) + ny * (p[1] - a[1])
        den = nx * ux + ny * uy
        if abs(den) < 1e-14:
            if dist_p < tol:
                return 0.0
            continue
        t = -dist_p / den
        if den > 0:
            t0 = max(t0, t)
        else:
            t1 = min(t1, t)
        if t0 >= t1:
            return 0.0
    return t1 - t0


def collinear_overlap(s1: Tuple[Point, Point], s2: Tuple[Point, Point],
                      tol: float = COLLINEAR_TOL) -> float:
    """Length of the common part of two segments lying on one line (else 0)."""
    p1, q1 = s1
    p2, q2 = s2
    if _dist_to_line(p1, q1, p2) >= tol or _dist_to_line(p1, q1, q2) >= tol:
        return 0.0
    dx, dy = q1[0] - p1[0], q1[1] - p1[1]
    L = math.hypot(dx, dy)
    if L == 0:
        return 0.0
    ux, uy = dx / L, dy / L
    a = (p2[0] - p1[0]) * ux + (p2[1] - p1[1]) * uy
    b = (q2[0] - p1[0]) * ux + (q2[1] - p1[1]) * uy
    lo, hi = max(0.0, min(a, b)), min(L, max(a, b))
    return max(0.0, hi - lo)


def is_convex(poly: Sequence[Point], tol: float = 1e-9) -> bool:
    """Is a counterclockwise polygon convex (up to ``tol`` per corner)?"""
    n = len(poly)
    for i in range(n):
        if _cross(poly[i - 1], poly[i], poly[(i + 1) % n]) < -tol:
            return False
    return True


def simplify(poly: Sequence[Point], tol: float = 1e-9) -> Polygon:
    """Drop vertices at which the boundary goes straight on."""
    pts = list(poly)
    changed = True
    while changed and len(pts) > 3:
        changed = False
        for i in range(len(pts)):
            a, b, c = pts[i - 1], pts[i], pts[(i + 1) % len(pts)]
            if (abs(_cross(a, b, c)) <= tol * max(1e-12, math.dist(a, c))
                    and (b[0] - a[0]) * (c[0] - b[0]) + (b[1] - a[1]) * (c[1] - b[1]) >= 0):
                del pts[i]
                changed = True
                break
    return pts


class Iso:
    """A planar isometry ``x -> A x + t``."""

    __slots__ = ("a", "b", "c", "d", "tx", "ty")

    def __init__(self, a=1.0, b=0.0, c=0.0, d=1.0, tx=0.0, ty=0.0):
        self.a, self.b, self.c, self.d, self.tx, self.ty = a, b, c, d, tx, ty

    def __call__(self, p: Point) -> Point:
        return (self.a * p[0] + self.b * p[1] + self.tx,
                self.c * p[0] + self.d * p[1] + self.ty)

    def compose(self, o: "Iso") -> "Iso":
        """``self o o``."""
        return Iso(self.a * o.a + self.b * o.c, self.a * o.b + self.b * o.d,
                   self.c * o.a + self.d * o.c, self.c * o.b + self.d * o.d,
                   self.a * o.tx + self.b * o.ty + self.tx,
                   self.c * o.tx + self.d * o.ty + self.ty)

    @property
    def det(self) -> float:
        return self.a * self.d - self.b * self.c

    def distance(self, o: "Iso") -> float:
        return max(abs(self.a - o.a), abs(self.b - o.b), abs(self.c - o.c),
                   abs(self.d - o.d), abs(self.tx - o.tx), abs(self.ty - o.ty))

    @staticmethod
    def reflection(p: Point, q: Point) -> "Iso":
        dx, dy = q[0] - p[0], q[1] - p[1]
        L = math.hypot(dx, dy)
        ux, uy = dx / L, dy / L
        a, b, c, d = 2 * ux * ux - 1, 2 * ux * uy, 2 * ux * uy, 2 * uy * uy - 1
        return Iso(a, b, c, d, p[0] - (a * p[0] + b * p[1]),
                   p[1] - (c * p[0] + d * p[1]))
