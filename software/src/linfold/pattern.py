"""Crease patterns: facets, creases, interior vertices, the folded image.

:class:`CreasePattern` turns a planar subdivision into the objects of the
paper:

* **facets**: the faces, merged across auxiliary (``F``) lines;
* **creases**: the pairs of facets separated by folded edges (``M``, ``V``,
  ``U``).  A crease may consist of several collinear edges; its layer
  variable, hence its assignment, is shared by all of them;
* **interior vertices**, each a :class:`linfold.vertex.Vertex` whose sectors
  are facets and whose creases are creases of the pattern, so that its rows
  are rows of the whole pattern;
* the **folding map**, a reflection across every crease, and the **side**
  ``p_i`` of every facet (Eq. (1));
* the **global rows**: all taco--tortilla and taco--taco constraints of the
  folded image, computed from the folded polygons, independently of the
  angular description used at the vertices.

Facets and creases are numbered from 0 in a deterministic order.
"""

from __future__ import annotations

import math
from collections import deque
from dataclasses import dataclass, field
from functools import cached_property
from itertools import combinations
from typing import Dict, List, Optional, Sequence, Set, Tuple

from . import geometry as G
from .formats import FOLDS, RawPattern, read_pattern
from .planar import PlanarGraph, planarise
from .rows import Row
from .vertex import Vertex, VertexError

__all__ = ["CreasePattern", "Crease", "PatternVertex", "Issue", "load"]

Point = Tuple[float, float]

#: tolerance on angles, in radians: crease rays closer than this coincide
ANGLE_TOL = 1e-6
#: tolerance on Kawasaki's alternating sum, in radians.  Patterns read from
#: files carry the precision of the program that wrote them; a genuine
#: violation is a whole sector's worth of angle.
KAWASAKI_TOL = 1e-4
#: relative tolerance on the single-valuedness of the folding map
MONODROMY_TOL = 1e-5


@dataclass
class Issue:
    """Something about the pattern that matters for the analysis."""

    kind: str           #: short machine-readable label
    message: str        #: explanation for a person
    fatal: bool         #: the pattern cannot fold flat because of it
    where: Optional[Point] = None


@dataclass
class Crease:
    id: int
    facets: Tuple[int, int]          #: smaller facet id first
    edges: List[int]                 #: indices into the planar graph's edges
    assignment: str                  #: 'M', 'V' or 'U'
    segment: Tuple[Point, Point]     #: endpoints of the whole crease (unit drawing)


@dataclass
class PatternVertex:
    id: int
    index: int                       #: index in the planar graph
    point: Point                     #: unit drawing
    creases: List[int]               #: crease ids, counterclockwise
    sectors: List[int]               #: facet ids; sector k lies before crease k
    angles: List[float]              #: radians
    vertex: Optional[Vertex] = None  #: None if Kawasaki fails or degree is odd
    problem: Optional[str] = None


class CreasePattern:
    """A crease pattern, ready for the analysis of :mod:`linfold.analysis`.

    Parameters
    ----------
    graph:
        the planar subdivision (see :func:`load` to read a file).
    angle_tol, kawasaki_tol:
        tolerances in radians (see the module constants).
    """

    def __init__(self, graph: PlanarGraph, name: str = "", *,
                 angle_tol: float = ANGLE_TOL, kawasaki_tol: float = KAWASAKI_TOL):
        self.graph = graph
        self.name = name
        self.angle_tol = angle_tol
        self.kawasaki_tol = kawasaki_tol
        self.issues: List[Issue] = []
        for p in graph.dangling_creases:
            self.issues.append(Issue(
                "dangling-crease", "a crease ends inside the sheet, at a vertex of "
                "degree one, where Kawasaki's condition cannot hold", True, p))
        self._build_facets()
        self._build_creases()
        self._build_parity()
        self._build_vertices()

    # ------------------------------------------------------------- facets
    def _build_facets(self):
        g = self.graph
        nf = len(g.faces)
        parent = list(range(nf))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for (u, v), a in zip(g.edges, g.assignments):
            if a in FOLDS or a == "B":
                continue
            f1, f2 = g.left.get((u, v), -1), g.left.get((v, u), -1)
            if f1 >= 0 and f2 >= 0:
                r1, r2 = find(f1), find(f2)
                if r1 != r2:
                    parent[max(r1, r2)] = min(r1, r2)
        roots = sorted({find(f) for f in range(nf)})
        rid = {r: i for i, r in enumerate(roots)}
        self.facet_of_face = [rid[find(f)] for f in range(nf)]
        self.n_facets = len(roots)
        self.facet_faces: List[List[int]] = [[] for _ in roots]
        for f in range(nf):
            self.facet_faces[self.facet_of_face[f]].append(f)

    def facet_left(self, u: int, v: int) -> int:
        """The facet on the left of the half-edge ``u -> v`` (-1 outside)."""
        f = self.graph.left.get((u, v), -1)
        return self.facet_of_face[f] if f >= 0 else -1

    @cached_property
    def facet_polygons(self) -> List[List[Point]]:
        """The boundary of every facet, counterclockwise, straight corners removed."""
        g = self.graph
        boundary: List[Dict[int, int]] = [dict() for _ in range(self.n_facets)]
        for u, v in g.edges:
            for a, b in ((u, v), (v, u)):
                fa, fb = self.facet_left(a, b), self.facet_left(b, a)
                if fa >= 0 and fa != fb:
                    boundary[fa][a] = b
        polys = []
        for f in range(self.n_facets):
            nxt = boundary[f]
            if not nxt:
                polys.append([])
                continue
            start = min(nxt)
            cyc, w = [start], nxt[start]
            guard = 0
            while w != start and guard <= len(nxt):
                cyc.append(w)
                w = nxt.get(w, start)
                guard += 1
            polys.append(G.simplify(G.ccw([g.vertices[i] for i in cyc])))
        return polys

    @cached_property
    def nonconvex_facets(self) -> List[int]:
        return [f for f, P in enumerate(self.facet_polygons)
                if len(P) < 3 or not G.is_convex(P)]

    def facet_point(self, f: int) -> Point:
        """A point inside facet ``f`` (unit drawing): the centroid of a face."""
        face = self.graph.faces[self.facet_faces[f][0]]
        pts = [self.graph.vertices[i] for i in face]
        # centroid of a fan triangle with positive area keeps the point inside
        # even for a non-convex face
        a = pts[0]
        best, area = None, 0.0
        for b, c in zip(pts[1:], pts[2:]):
            s = (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])
            if s > area:
                best, area = ((a[0] + b[0] + c[0]) / 3, (a[1] + b[1] + c[1]) / 3), s
        return best or a

    # ------------------------------------------------------------ creases
    def _build_creases(self):
        g = self.graph
        by_pair: Dict[Tuple[int, int], List[int]] = {}
        for k, ((u, v), a) in enumerate(zip(g.edges, g.assignments)):
            if a not in FOLDS:
                continue
            f1, f2 = self.facet_left(u, v), self.facet_left(v, u)
            if f1 < 0 or f2 < 0:
                self.issues.append(Issue(
                    "crease-on-boundary", "an edge on the boundary of the sheet is "
                    "labelled as a fold; it is ignored", False, self._orig(g.vertices[u])))
                continue
            if f1 == f2:
                self.issues.append(Issue(
                    "crease-inside-facet", "a folded edge has the same facet on "
                    "both sides (it ends inside the sheet)", True,
                    self._orig(g.vertices[u])))
                continue
            by_pair.setdefault((min(f1, f2), max(f1, f2)), []).append(k)
        self.creases: List[Crease] = []
        self.crease_of_pair: Dict[Tuple[int, int], int] = {}
        self.crease_of_edge: Dict[int, int] = {}
        for pair in sorted(by_pair):
            ks = by_pair[pair]
            labels = {g.assignments[k] for k in ks} - {"U"}
            if len(labels) > 1:
                self.issues.append(Issue(
                    "assignment-conflict", "the edges of one crease carry both a "
                    "mountain and a valley label; they separate the same two "
                    "facets, so their assignments must agree", True,
                    self._orig(g.vertices[g.edges[ks[0]][0]])))
            a = labels.pop() if len(labels) == 1 else "U"
            ends = [g.vertices[i] for k in ks for i in g.edges[k]]
            p0 = ends[0]
            far = max(ends, key=lambda q: math.dist(p0, q))
            near = max(ends, key=lambda q: math.dist(far, q))
            c = Crease(len(self.creases), pair, ks, a, (near, far))
            self.crease_of_pair[pair] = c.id
            for k in ks:
                self.crease_of_edge[k] = c.id
            self.creases.append(c)

    # ------------------------------------------------------------- parity
    def _build_parity(self):
        adj: Dict[int, List[int]] = {f: [] for f in range(self.n_facets)}
        for c in self.creases:
            a, b = c.facets
            adj[a].append(b)
            adj[b].append(a)
        side = [0] * self.n_facets
        self.bipartite = True
        self.n_components = 0
        for s in range(self.n_facets):
            if side[s]:
                continue
            self.n_components += 1
            side[s] = 1
            queue = deque([s])
            while queue:
                i = queue.popleft()
                for j in adj[i]:
                    if side[j] == 0:
                        side[j] = -side[i]
                        queue.append(j)
                    elif side[j] == side[i]:
                        self.bipartite = False
        self.side = side
        if not self.bipartite:
            self.issues.append(Issue(
                "not-bipartite", "the facets cannot be coloured with two colours "
                "alternating across every crease, so no flat folding exists "
                "(some vertex has odd degree)", True))

    # ----------------------------------------------------------- vertices
    def _build_vertices(self):
        g = self.graph
        fold_nbrs: Dict[int, List[Tuple[int, int]]] = {}
        for k, (u, v) in enumerate(g.edges):
            if k in self.crease_of_edge:
                fold_nbrs.setdefault(u, []).append((v, k))
                fold_nbrs.setdefault(v, []).append((u, k))
        self.vertices: List[PatternVertex] = []
        self.straight_vertices = 0
        for w in sorted(fold_nbrs):
            if w in g.outer:
                continue
            here = g.vertices[w]
            items = sorted(fold_nbrs[w], key=lambda it: math.atan2(
                g.vertices[it[0]][1] - here[1], g.vertices[it[0]][0] - here[0]))
            dirs = [math.atan2(g.vertices[o][1] - here[1], g.vertices[o][0] - here[0])
                    for o, _ in items]
            d = len(items)
            angles = []
            for i in range(d):
                a = dirs[(i + 1) % d] - dirs[i]
                while a <= 0:
                    a += 2 * math.pi
                angles.append(a)
            # sector i lies between fold edges i and i+1 (counterclockwise) and
            # is the facet on the left of edge i; crease i is fold edge i+1
            sectors = [self.facet_left(w, items[i][0]) for i in range(d)]
            creases = [self.crease_of_edge[items[(i + 1) % d][1]] for i in range(d)]
            if d == 2 and abs(angles[0] - math.pi) < self.kawasaki_tol:
                self.straight_vertices += 1
                continue
            pv = PatternVertex(len(self.vertices), w, here, creases, sectors, angles)
            xy = self._orig(here)
            if d % 2:
                pv.problem = f"odd degree {d}"
                self.issues.append(Issue(
                    "odd-degree", f"an interior vertex has odd degree {d}; Maekawa's "
                    "theorem forbids it in a flat folding", True, xy))
            else:
                self._make_vertex(pv)
            self.vertices.append(pv)

    def _make_vertex(self, pv: PatternVertex) -> None:
        """Build the :class:`Vertex` of an interior vertex of even degree.

        Kawasaki's alternating sum must vanish to ``kawasaki_tol``; its
        residual is then spread evenly over the steps of the walk, and crease
        positions closer than ``max(angle_tol, 2 |residual|)`` are taken to
        coincide.  Two positions just above that tolerance are reported: they
        are neither clearly equal nor clearly distinct.
        """
        n = len(pv.angles)
        resid = sum(a if j % 2 == 0 else -a for j, a in enumerate(pv.angles))
        xy = self._orig(pv.point)
        if abs(resid) > self.kawasaki_tol:
            pv.problem = f"Kawasaki's condition fails (alternating sum {resid:.3g} rad)"
            self.issues.append(Issue(
                "kawasaki", f"Kawasaki's condition fails at an interior vertex: the "
                f"alternating sum of its angles is {math.degrees(resid):.4g} degrees",
                True, xy))
            return
        angles = [a - (resid / n if j % 2 == 0 else -resid / n)
                  for j, a in enumerate(pv.angles)]
        tol = max(self.angle_tol, 2 * abs(resid))
        try:
            sides = [self.side[f] for f in pv.sectors] if self.bipartite else None
            v = Vertex(angles, tol=tol, parity=sides,
                       crease_names=[f"c{c}" for c in pv.creases],
                       sector_names=[f"F{f}" for f in pv.sectors])
        except VertexError as exc:
            pv.problem = str(exc)
            self.issues.append(Issue("vertex", str(exc), True, xy))
            return
        pv.vertex = v
        if v.min_gap is not None and v.min_gap < 100 * tol:
            self.issues.append(Issue(
                "ambiguous-angles", f"two crease rays at this vertex differ by "
                f"{v.min_gap:.2e} rad in the folded image, close to the tolerance "
                f"{tol:.1e}; check the precision of the coordinates", False, xy))

    # ------------------------------------------------------------ helpers
    def _orig(self, p: Point) -> Point:
        return self.graph.to_original(p)

    def original(self, p: Point) -> Point:
        """Coordinates of a point of the unit drawing in the file's units."""
        return self._orig(p)

    @property
    def interior_vertices(self) -> List[PatternVertex]:
        return self.vertices

    @property
    def fatal_issues(self) -> List[Issue]:
        return [i for i in self.issues if i.fatal]

    def local_rows(self, pv: PatternVertex) -> List[Row]:
        """The rows at an interior vertex, written on facets and creases."""
        v = pv.vertex
        out = []
        for r in v.rows:
            terms = tuple((pv.sectors[a], pv.sectors[b]) for a, b in r.terms)
            creases = tuple(pv.creases[k] for k in r.creases)
            tort = pv.sectors[r.tortilla] if r.tortilla is not None else None
            out.append(Row(r.kind, creases, tort, terms, pv.id))
        return out

    # -------------------------------------------------------- folding map
    @cached_property
    def folding(self) -> "Folding":
        return Folding(self)


@dataclass
class Folding:
    """The folding map and everything read off the folded image."""

    cp: CreasePattern
    iso: List[Optional[G.Iso]] = field(default_factory=list)
    images: List[List[Point]] = field(default_factory=list)
    monodromy: float = 0.0
    ok: bool = True
    message: str = ""

    def __post_init__(self):
        cp = self.cp
        adj: Dict[int, List[Tuple[int, int]]] = {f: [] for f in range(cp.n_facets)}
        for c in cp.creases:
            a, b = c.facets
            adj[a].append((b, c.id))
            adj[b].append((a, c.id))
        iso: List[Optional[G.Iso]] = [None] * cp.n_facets
        for s in range(cp.n_facets):
            if iso[s] is not None:
                continue
            iso[s] = G.Iso()
            queue = deque([s])
            while queue:
                i = queue.popleft()
                for j, cid in adj[i]:
                    if iso[j] is None:
                        p, q = cp.creases[cid].segment
                        iso[j] = iso[i].compose(G.Iso.reflection(p, q))
                        queue.append(j)
        worst = 0.0
        for c in cp.creases:
            a, b = c.facets
            p, q = c.segment
            worst = max(worst, iso[a].compose(G.Iso.reflection(p, q)).distance(iso[b]))
        self.iso = iso
        self.monodromy = worst
        if worst > MONODROMY_TOL:
            self.ok = False
            self.message = (f"the folding map is not single-valued (mismatch "
                            f"{worst:.1e}): Kawasaki's condition fails somewhere")
        self.images = [G.ccw([iso[f](p) for p in P])
                       for f, P in enumerate(cp.facet_polygons)]
        self.boxes = [G.bbox(P) if P else (0, 0, 0, 0) for P in self.images]

    # --------------------------------------------------------------- overlaps
    @cached_property
    def overlaps(self) -> List[Tuple[int, int]]:
        """Pairs of facets whose images meet in positive area."""
        out = []
        for a, b in self._box_pairs(self.boxes, self.boxes):
            if a < b and G.intersection_area([self.images[a], self.images[b]]) > G.AREA_TOL:
                out.append((a, b))
        return sorted(out)

    @cached_property
    def overlap_set(self) -> Set[Tuple[int, int]]:
        return set(self.overlaps)

    def overlapping(self, a: int, b: int) -> bool:
        return (min(a, b), max(a, b)) in self.overlap_set

    @staticmethod
    def _box_pairs(boxes_a, boxes_b, pad: float = 1e-9):
        """Index pairs whose boxes intersect (sort and sweep on x)."""
        ev = sorted([(bx[0] - pad, 0, i) for i, bx in enumerate(boxes_a)] +
                    [(bx[0] - pad, 1, j) for j, bx in enumerate(boxes_b)])
        act_a: List[int] = []
        act_b: List[int] = []
        for x, side, i in ev:
            if side == 0:
                act_b = [j for j in act_b if boxes_b[j][2] + pad >= x]
                bx = boxes_a[i]
                for j in act_b:
                    by = boxes_b[j]
                    if by[1] <= bx[3] + pad and bx[1] <= by[3] + pad:
                        yield i, j
                act_a.append(i)
            else:
                act_a = [k for k in act_a if boxes_a[k][2] + pad >= x]
                by = boxes_b[i]
                for k in act_a:
                    bx = boxes_a[k]
                    if by[1] <= bx[3] + pad and bx[1] <= by[3] + pad:
                        yield k, i
                act_b.append(i)

    # ------------------------------------------------------------------ rows
    def crease_images(self) -> List[List[Tuple[Point, Point]]]:
        cp = self.cp
        out = []
        for c in cp.creases:
            T = self.iso[c.facets[0]]
            out.append([(T(cp.graph.vertices[u]), T(cp.graph.vertices[v]))
                        for u, v in (cp.graph.edges[k] for k in c.edges)])
        return out

    @cached_property
    def rows(self) -> List[Row]:
        """All taco--tortilla and taco--taco rows of the folded pattern."""
        cp = self.cp
        imgs = self.crease_images()
        out: List[Row] = []
        # taco--tortilla: a crease image through the interior of a facet image
        seg_boxes, seg_owner = [], []
        for cid, segs in enumerate(imgs):
            for p, q in segs:
                seg_boxes.append((min(p[0], q[0]), min(p[1], q[1]),
                                  max(p[0], q[0]), max(p[1], q[1])))
                seg_owner.append((cid, p, q))
        hits: Set[Tuple[int, int]] = set()
        for si, f in self._box_pairs(seg_boxes, self.boxes):
            cid, p, q = seg_owner[si]
            i, j = cp.creases[cid].facets
            if f in (i, j) or (cid, f) in hits:
                continue
            if G.inside_length(p, q, self.images[f]) > G.LEN_TOL:
                hits.add((cid, f))
        for cid, f in sorted(hits):
            i, j = cp.creases[cid].facets
            out.append(Row("TT", (cid,), f, ((i, f), (j, f))))
        # taco--taco: two crease images overlapping along a common line
        pairs: Set[Tuple[int, int]] = set()
        for s1, s2 in self._box_pairs(seg_boxes, seg_boxes):
            c1, p1, q1 = seg_owner[s1]
            c2, p2, q2 = seg_owner[s2]
            if c1 >= c2 or (c1, c2) in pairs:
                continue
            i, j = cp.creases[c1].facets
            k, l = cp.creases[c2].facets
            if len({i, j, k, l}) < 4:
                continue
            if G.collinear_overlap((p1, q1), (p2, q2)) <= G.LEN_TOL:
                continue
            if G.intersection_area([self.images[x] for x in (i, j, k, l)]) > G.AREA_TOL:
                pairs.add((c1, c2))
        for c1, c2 in sorted(pairs):
            i, j = cp.creases[c1].facets
            k, l = cp.creases[c2].facets
            out.append(Row("TC", (c1, c2), None, ((i, k), (j, k), (i, l), (j, l))))
        return out

    def triples(self, cap: int = 2_000_000) -> Tuple[List[Tuple[int, int, int]], bool]:
        """Triples of facets with a common region (the transitivity family).

        Returns ``(triples, complete)``; enumeration stops after ``cap``.
        """
        nb: Dict[int, Set[int]] = {}
        for a, b in self.overlaps:
            nb.setdefault(a, set()).add(b)
            nb.setdefault(b, set()).add(a)
        out = []
        for a, b in self.overlaps:
            for c in sorted(nb[a] & nb[b]):
                if c <= b:
                    continue
                if G.intersection_area([self.images[a], self.images[b],
                                        self.images[c]]) > G.AREA_TOL:
                    out.append((a, b, c))
                    if len(out) >= cap:
                        return out, False
        return out, True


def load(path: str, **kwargs) -> CreasePattern:
    """Read a crease-pattern file (FOLD, CP, OPX or SVG)."""
    import os
    raw = read_pattern(path)
    cp = CreasePattern(planarise(raw), name=os.path.basename(path), **kwargs)
    cp.raw = raw
    return cp


def from_segments(segments: Sequence[Tuple[Point, Point, str]], name: str = "",
                  **kwargs) -> CreasePattern:
    """Build a pattern from ``(p, q, assignment)`` segments."""
    from .formats import _Builder
    b = _Builder()
    for p, q, a in segments:
        b.segment(p, q, a)
    raw = b.build("", "segments")
    cp = CreasePattern(planarise(raw), name=name, **kwargs)
    cp.raw = raw
    return cp
