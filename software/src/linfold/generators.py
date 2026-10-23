"""Small crease patterns used in the paper, the examples and the tests.

Every function returns a list of segments ``(p, q, assignment)``; pass it to
:func:`linfold.pattern.from_segments` for a :class:`CreasePattern`, or to
:func:`write_segments` for a FOLD file.
"""

from __future__ import annotations

import math
from typing import List, Optional, Sequence, Tuple

__all__ = ["single_vertex", "triangle", "grid", "miura", "write_segments"]

Point = Tuple[float, float]
Segment = Tuple[Point, Point, str]


def _ray_to_square(theta: float, half: float) -> Point:
    """Where the ray from the origin at angle ``theta`` leaves ``[-h, h]^2``."""
    c, s = math.cos(theta), math.sin(theta)
    t = min(half / abs(c) if abs(c) > 1e-15 else math.inf,
            half / abs(s) if abs(s) > 1e-15 else math.inf)
    return (t * c, t * s)


def _square(half: float) -> List[Segment]:
    cs = [(-half, -half), (half, -half), (half, half), (-half, half)]
    return [(cs[i], cs[(i + 1) % 4], "B") for i in range(4)]


def single_vertex(angles_deg: Sequence[float], labels: Optional[str] = None,
                  half: float = 1.0) -> List[Segment]:
    """One vertex at the centre of a square sheet.

    The creases leave the centre at the angles ``0, a1, a1+a2, ...``
    (degrees, counterclockwise), so that the sector between the creases at
    ``0`` and ``a1`` is ``f1``; crease ``k`` of the list ends sector ``k``.
    ``labels`` is a word in ``M``, ``V``, ``U`` (``e1`` first).
    """
    n = len(angles_deg)
    labels = labels or "U" * n
    segs = _square(half)
    theta = 0.0
    for k in range(n):
        theta += math.radians(angles_deg[k])
        segs.append(((0.0, 0.0), _ray_to_square(theta, half), labels[k]))
    return segs


def triangle(angles_deg: Sequence[float] = (60, 100, 120, 80), radius: float = 1.0,
             half: float = 3.2, labels: Optional[str] = None) -> List[Segment]:
    """Three degree-four vertices around a triangle (Sec. 8, Fig. 6b).

    At each corner of an equilateral triangle the sector inside the triangle
    has angle ``angles_deg[0]`` and is smaller than its two neighbours, so the
    big--little--big lemma makes the two triangle edges at that corner
    opposite; three edges cannot be pairwise opposite.  Kawasaki's condition
    holds at every vertex and every vertex folds flat on its own.
    """
    P = [(radius * math.cos(math.radians(90 + 120 * k)),
          radius * math.sin(math.radians(90 + 120 * k))) for k in range(3)]
    lab = labels or "U" * 9
    segs = _square(half)
    for k in range(3):
        segs.append((P[k], P[(k + 1) % 3], lab[k]))
    _, a1, a2, _ = angles_deg
    i = 3
    for k in range(3):
        A, B = P[k], P[(k + 2) % 3]
        d = math.degrees(math.atan2(B[1] - A[1], B[0] - A[0]))
        for t in (d + a1, d + a1 + a2):
            th = math.radians(t)
            c, s = math.cos(th), math.sin(th)
            # leave the square from A
            ts = []
            for val, comp, org in ((half, c, A[0]), (-half, c, A[0]),
                                   (half, s, A[1]), (-half, s, A[1])):
                if abs(comp) > 1e-15:
                    tt = (val - org) / comp
                    if tt > 0:
                        ts.append(tt)
            tt = min(x for x in ts
                     if abs(A[0] + x * c) <= half + 1e-9 and abs(A[1] + x * s) <= half + 1e-9)
            segs.append((A, (A[0] + tt * c, A[1] + tt * s), lab[i]))
            i += 1
    return segs


def grid(m: int, n: int, labels: str = "U") -> List[Segment]:
    """An ``m x n`` map: unit squares, every crease with the same label."""
    segs = []
    for i in range(m + 1):
        a = "B" if i in (0, m) else labels
        for j in range(n):
            segs.append(((float(i), float(j)), (float(i), float(j + 1)), a))
    for j in range(n + 1):
        a = "B" if j in (0, n) else labels
        for i in range(m):
            segs.append(((float(i), float(j)), (float(i + 1), float(j)), a))
    return segs


def miura(m: int, n: int, angle_deg: float = 70.0, width: float = 1.0,
          height: float = 1.0) -> List[Segment]:
    """A Miura-ori of ``m x n`` parallelograms, creases unassigned.

    The zigzag lines are horizontal (``n + 1`` of them, ``n - 1`` creases),
    the straight lines are ``m - 1`` columns of slanted segments.
    """
    shift = height / math.tan(math.radians(angle_deg))
    def pt(i, j):
        return (i * width + (shift if j % 2 else 0.0), j * height)
    segs = []
    for j in range(n + 1):
        a = "B" if j in (0, n) else "U"
        for i in range(m):
            segs.append((pt(i, j), pt(i + 1, j), a))
    for i in range(m + 1):
        a = "B" if i in (0, m) else "U"
        for j in range(n):
            segs.append((pt(i, j), pt(i, j + 1), a))
    return segs


def write_segments(path: str, segments: Sequence[Segment], title: str = "") -> None:
    """Write segments as a FOLD crease pattern (shared endpoints merged)."""
    from .formats import _Builder, write_fold
    b = _Builder(1e-12)
    for p, q, a in segments:
        b.segment(p, q, a)
    write_fold(path, b.vertices, b.edges, b.assignments, title=title)
