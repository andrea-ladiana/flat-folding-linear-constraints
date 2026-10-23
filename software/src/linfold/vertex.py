"""The linear constraints at a single vertex (Secs. 2--7 of the paper).

A vertex of degree ``n`` is given by its sector angles
``alpha_1, ..., alpha_n`` in cyclic order.  In the folded image the sector
``f_k`` becomes the angular interval between ``c_{k-1}`` and ``c_k``, where

    c_0 = 0,    c_k = c_{k-1} + (-1)^(k+1) alpha_k        (Eq. (4))

and the crease ``e_k`` (between ``f_k`` and ``f_{k+1}``) lies on the ray
``c_k``; Kawasaki's condition is ``c_n = 0``.  Everything at the vertex is
determined by this *walk*:

* the taco--tortilla and taco--taco rows (Lemma 1, :attr:`Vertex.rows`);
* the hypergraph of the rows and its components, which cut out the space
  ``W_lin(v)`` of mountain--valley assignments induced by the solutions
  (Lemma 3, :attr:`Vertex.components`, :attr:`Vertex.relations`);
* at a vertex without taco--taco rows, the pairing of the creases into one
  pair forced equal and ``m - 1`` pairs forced opposite (Theorem 2,
  :attr:`Vertex.pairs`), which are the persistence pairs of the walk
  (Theorem 3, :meth:`Vertex.persistence_pairs`);
* Hull's crimping recursion and its blocks, which coincide with the
  components (Theorem 4, :attr:`Vertex.hull`).

Indices are 0-based in the code: sector ``i`` lies between creases ``i - 1``
and ``i``, so crease ``i`` separates sectors ``i`` and ``i + 1`` (mod ``n``).
Printed names are 1-based, as in the paper (``e1``, ``f1``).  Mountain is
``+1`` and valley ``-1``; in bit form, ``s = 0`` is a mountain and ``s = 1``
a valley.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from functools import cached_property
from itertools import combinations
from typing import Dict, List, Optional, Sequence, Tuple, Union

from .f2 import AffineSystem
from .hull import HullRecursion, hull_recursion
from .rows import Row, canonical

__all__ = ["Vertex", "VertexError", "Component", "Relation", "PairInfo",
           "AssignmentCheck", "parse_assignment"]

Number = Union[int, float, Fraction]


class VertexError(ValueError):
    """The angles do not describe a closed walk (a flat-foldable vertex)."""


class InternalError(RuntimeError):
    """Two independent computations that the paper proves equal disagree."""


# --------------------------------------------------------------------- data
@dataclass(frozen=True)
class Relation:
    """A linear relation on the assignment: ``sum(s_k for k in creases) = parity``.

    ``s_k = 1`` when the crease ``k`` is a valley.  Equivalently, the number
    of valleys among ``creases`` has the given parity, or
    ``M - V = len(creases) - 2*parity (mod 4)`` on them.
    """

    creases: Tuple[int, ...]
    parity: int

    @property
    def size(self) -> int:
        return len(self.creases)

    @property
    def is_pair(self) -> bool:
        return len(self.creases) == 2

    @property
    def equal(self) -> Optional[bool]:
        """For a pair: ``True`` if forced equal, ``False`` if opposite."""
        if not self.is_pair:
            return None
        return self.parity == 0

    @property
    def mv_mod4(self) -> int:
        return (len(self.creases) - 2 * self.parity) % 4

    def holds(self, bits: Sequence[int]) -> bool:
        return sum(bits[k] for k in self.creases) % 2 == self.parity


@dataclass
class Component:
    """A connected component of the hypergraph ``H_v`` of the rows."""

    pairs: List[Tuple[int, int]]      #: its vertices: overlapping sector pairs
    rows: List[int]                   #: indices into :attr:`Vertex.rows`
    creases: Tuple[int, ...]          #: creases whose adjacent pair it contains
    kappa: int                        #: constant of the sum of its rows
    relation: Optional[Relation]      #: the relation it imposes (None if no crease)


@dataclass
class PairInfo:
    """A pair of creases joined by a path of the row graph (Theorem 2)."""

    creases: Tuple[int, int]
    equal: bool
    rows: List[int]                   #: the rows of the path, end to end


@dataclass
class AssignmentCheck:
    """The verdict of :meth:`Vertex.check` on a mountain--valley assignment."""

    sigma: Tuple[int, ...]
    mv: int                                     #: M - V
    maekawa_mod4: bool                          #: M - V = 2 (mod 4)
    maekawa: bool                               #: M - V = +-2
    violated: List[Component]                   #: components whose relation fails
    in_wlin: bool                               #: induced by a solution of the rows
    flat_foldable: bool                         #: Hull's recursion accepts it
    hull_failure: Optional[dict]                #: first failing step of the recursion
    big_little_big: List[Tuple[int, int, int]]  #: (sector, crease, crease) violated


def parse_assignment(word, n: int) -> Tuple[int, ...]:
    """``'MMVV'`` or ``[1, 1, -1, -1]`` -> ``(1, 1, -1, -1)`` (mountain = +1)."""
    if isinstance(word, str):
        w = word.replace(" ", "").replace(",", "").upper()
        if len(w) != n or any(ch not in "MV" for ch in w):
            raise ValueError(f"expected {n} letters M or V, got {word!r}")
        return tuple(1 if ch == "M" else -1 for ch in w)
    out = tuple(int(s) for s in word)
    if len(out) != n or any(s not in (1, -1) for s in out):
        raise ValueError(f"expected {n} values +1 (mountain) or -1 (valley)")
    return out


def _cluster(values: Sequence[Number], tol: Number):
    """Snap values that lie within ``tol`` of each other (single linkage).

    Returns ``(snapped, spread, gap)``: the snapped values, in the input
    order; the largest spread of a cluster; the smallest distance between two
    clusters (``None`` if there is one cluster).
    """
    order = sorted(range(len(values)), key=lambda i: values[i])
    groups: List[List[int]] = []
    for i in order:
        if groups and values[i] - values[groups[-1][-1]] <= tol:
            groups[-1].append(i)
        else:
            groups.append([i])
    out = list(values)
    spread = 0
    reps = []
    for g in groups:
        vals = [values[i] for i in g]
        if len(g) == 1 or tol == 0:
            rep = vals[0]
        else:
            rep = sum(vals) / len(vals)
            spread = max(spread, max(vals) - min(vals))
        for i in g:
            out[i] = rep
        reps.append(rep)
    gap = min((b - a for a, b in zip(reps, reps[1:])), default=None)
    return out, spread, gap


# ------------------------------------------------------------------- vertex
class Vertex:
    """A single vertex, or more generally a closed walk (Sec. 3).

    Parameters
    ----------
    angles:
        the sector angles in cyclic order, in any unit.  Integers, fractions
        or decimal strings are handled exactly; floats are compared with the
        tolerance ``tol``.
    tol:
        two crease positions closer than ``tol`` are taken to coincide, and
        Kawasaki's alternating sum may deviate from zero by ``tol`` (the
        residual is then spread evenly over the steps of the walk).
    parity:
        the side ``p_k = +1/-1`` of every sector (Eq. (1)); alternating,
        starting with ``+1``, by default.  Only the relations written in
        terms of layer variables depend on it.
    crease_names, sector_names:
        names used in printed output (default ``e1, e2, ...``, ``f1, ...``).
    """

    def __init__(self, angles: Sequence, *, tol: Number = 0,
                 parity: Optional[Sequence[int]] = None,
                 crease_names: Optional[Sequence[str]] = None,
                 sector_names: Optional[Sequence[str]] = None):
        angles = [Fraction(a) if isinstance(a, str) else a for a in angles]
        n = len(angles)
        if n < 2 or n % 2:
            raise VertexError(f"a flat-foldable vertex has even degree, got {n}")
        if any(a <= 0 for a in angles):
            raise VertexError("sector angles must be positive")
        self.n = n
        self.m = n // 2
        self.angles = list(angles)
        self.tol = tol
        resid = sum(a if j % 2 == 0 else -a for j, a in enumerate(angles))
        self.kawasaki_residual = resid
        if abs(resid) > tol:
            raise VertexError(
                f"Kawasaki's condition fails: the alternating sum of the angles "
                f"is {float(resid):.6g}, not 0")
        raw, c = [], 0
        for j, a in enumerate(angles):
            c = c + a if j % 2 == 0 else c - a
            raw.append(c)
        if resid != 0:
            raw = [p - (i + 1) * resid / n for i, p in enumerate(raw)]
        raw[-1] = raw[-1] * 0          # exactly zero, in the right type
        self.pos, self.cluster_spread, self.min_gap = _cluster(raw, tol)
        for i in range(n):
            if self.pos[i] == self.pos[i - 1]:
                raise VertexError(f"sector {i + 1} has angle below the tolerance")
        if parity is None:
            parity = [1 if i % 2 == 0 else -1 for i in range(n)]
        parity = [int(p) for p in parity]
        if len(parity) != n or any(parity[i] != -parity[i - 1] for i in range(n)):
            raise VertexError("the sides p_k must alternate around the vertex")
        self.parity = parity
        self.crease_names = list(crease_names) if crease_names else [
            f"e{k + 1}" for k in range(n)]
        self.sector_names = list(sector_names) if sector_names else [
            f"f{k + 1}" for k in range(n)]

    # ------------------------------------------------------------ geometry
    def __repr__(self) -> str:
        return f"Vertex({self.angles!r})"

    def interval(self, i: int) -> Tuple[Number, Number]:
        """The interval ``I_i`` of sector ``i`` in the folded image."""
        a, b = self.pos[i - 1], self.pos[i]
        return (a, b) if a < b else (b, a)

    def length(self, i: int) -> Number:
        lo, hi = self.interval(i)
        return hi - lo

    def is_max(self, k: int) -> bool:
        """Is crease ``k`` a local maximum of the walk?"""
        return self.pos[k] > self.pos[k - 1]

    def nxt(self, i: int) -> int:
        return (i + 1) % self.n

    def adjacent_pair(self, k: int) -> Tuple[int, int]:
        """The sectors of crease ``k``, smaller index first."""
        a, b = k, self.nxt(k)
        return (a, b) if a < b else (b, a)

    @cached_property
    def generic(self) -> bool:
        """No two creases on one ray of the folded image."""
        return len(set(self.pos)) == self.n

    @cached_property
    def overlapping_pairs(self) -> List[Tuple[int, int]]:
        out = []
        for a, b in combinations(range(self.n), 2):
            la, ha = self.interval(a)
            lb, hb = self.interval(b)
            if min(ha, hb) > max(la, lb):
                out.append((a, b))
        return out

    @cached_property
    def top(self) -> List[int]:
        """Creases at the highest ray of the folded image."""
        h = max(self.pos)
        return [k for k in range(self.n) if self.pos[k] == h]

    @cached_property
    def bottom(self) -> List[int]:
        """Creases at the lowest ray of the folded image."""
        h = min(self.pos)
        return [k for k in range(self.n) if self.pos[k] == h]

    # ---------------------------------------------------------------- rows
    @cached_property
    def rows(self) -> List[Row]:
        """The taco--tortilla and taco--taco rows at the vertex (Lemma 1)."""
        n, pos = self.n, self.pos
        out: List[Row] = []
        for k in range(n):
            a, b = k, self.nxt(k)
            for g in range(n):
                if g in (a, b):
                    continue
                lo, hi = self.interval(g)
                if lo < pos[k] < hi:
                    out.append(Row("TT", (k,), g, ((a, g), (b, g))))
        for k, l in combinations(range(n), 2):
            if pos[k] == pos[l] and self.is_max(k) == self.is_max(l):
                k1, l1 = self.nxt(k), self.nxt(l)
                out.append(Row("TC", (k, l), None,
                               ((k, l), (k1, l), (k, l1), (k1, l1))))
        return out

    @cached_property
    def tt_rows(self) -> List[Row]:
        return [r for r in self.rows if r.kind == "TT"]

    @cached_property
    def tc_rows(self) -> List[Row]:
        return [r for r in self.rows if r.kind == "TC"]

    @property
    def has_tc(self) -> bool:
        return bool(self.tc_rows)

    def layer_system(self) -> AffineSystem:
        """The rows as an affine system on the overlapping pairs ``x_ab``, a < b."""
        sysm = AffineSystem()
        for p in self.overlapping_pairs:
            sysm.var(p)
        for i, r in enumerate(self.rows):
            pairs, const = r.equation()
            sysm.add([sysm.column(p) for p in pairs], const, tag=i)
        return sysm

    # ---------------------------------------------------- Theorem 1, Lemma 2
    def pair_multiplicities(self) -> Dict[Tuple[int, int], int]:
        """How many rows contain each overlapping pair (Lemma 2: 1 or 2)."""
        mult = {p: 0 for p in self.overlapping_pairs}
        for r in self.rows:
            for a, b in r.terms:
                mult[(min(a, b), max(a, b))] += 1
        return mult

    def sum_of_rows(self):
        """``(pairs, const)``: the F2-sum of all the rows, canonically oriented."""
        terms = [t for r in self.rows for t in r.terms]
        return canonical(terms)

    def vertex_row(self):
        """``(pairs, const)``: the vertex row ``sum_k x_{k,k+1} = 1`` (Eq. (2))."""
        pairs, const = canonical([(k, self.nxt(k)) for k in range(self.n)])
        return pairs, const ^ 1

    def theorem1_holds(self) -> bool:
        """Theorem 1: the sum of the rows is the vertex row."""
        return self.sum_of_rows() == self.vertex_row()

    def gauge_homogeneous(self) -> bool:
        """Proof of Theorem 1: numbered from a lowest crease, every row is
        homogeneous (constant 0 in the canonical orientation)."""
        B = self.bottom[0]
        new = lambda i: (i - B - 1) % self.n      # noqa: E731
        return all(canonical(r.terms, key=new)[1] == 0 for r in self.rows)

    # ------------------------------------------------- hypergraph, Lemma 3
    @cached_property
    def components(self) -> List[Component]:
        """The components of the hypergraph ``H_v`` (Sec. 5)."""
        pairs = self.overlapping_pairs
        index = {p: i for i, p in enumerate(pairs)}
        parent = list(range(len(pairs)))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for r in self.rows:
            ids = [index[(min(a, b), max(a, b))] for a, b in r.terms]
            for j in ids[1:]:
                ra, rb = find(ids[0]), find(j)
                if ra != rb:
                    parent[rb] = ra
        groups: Dict[int, List[int]] = {}
        for i in range(len(pairs)):
            groups.setdefault(find(i), []).append(i)
        rows_of: Dict[int, List[int]] = {}
        for ri, r in enumerate(self.rows):
            a, b = r.terms[0]
            rows_of.setdefault(find(index[(min(a, b), max(a, b))]), []).append(ri)
        creases_of: Dict[int, List[int]] = {}
        for k in range(self.n):
            creases_of.setdefault(find(index[self.adjacent_pair(k)]), []).append(k)

        out = []
        for root, members in sorted(groups.items(), key=lambda kv: min(kv[1])):
            rws = rows_of.get(root, [])
            terms = [t for ri in rws for t in self.rows[ri].terms]
            _, kappa = canonical(terms)
            cr = tuple(creases_of.get(root, []))
            rel = None
            if cr:
                # s_k = x_{k,k+1} + [p_k = -1], and x_{k,k+1} is the canonical
                # adjacent variable plus one when the pair is written backwards
                par = kappa
                for k in cr:
                    par ^= int(k > self.nxt(k)) ^ int(self.parity[k] < 0)
                rel = Relation(cr, par)
            out.append(Component([pairs[i] for i in members], rws, cr, kappa, rel))
        return out

    @cached_property
    def relations(self) -> List[Relation]:
        """The relations cutting out ``W_lin(v)``, one per component (Lemma 3)."""
        return [c.relation for c in self.components if c.relation is not None]

    @property
    def gamma(self) -> int:
        """The number of components containing adjacent pairs."""
        return len(self.relations)

    @property
    def dim_wlin(self) -> int:
        """``dim W_lin(v) = n - gamma`` (Lemma 3)."""
        return self.n - self.gamma

    @property
    def wlin_count(self) -> int:
        return 2 ** self.dim_wlin

    # ------------------------------------------------ Theorem 2, Prop. 1-2
    @cached_property
    def pairs(self) -> Optional[List[PairInfo]]:
        """The pairing of Theorem 2 (``None`` at a vertex with taco--taco rows).

        Every pair is joined by a path of the row graph; the path of the two
        extreme creases forces them equal, every other path forces opposite
        assignments.
        """
        if self.has_tc:
            return None
        out = []
        for comp in self.components:
            if not comp.creases:
                continue
            if len(comp.creases) != 2:
                raise InternalError("a path of the row graph without two ends")
            out.append(PairInfo(tuple(comp.creases), comp.relation.equal,
                                self._path_order(comp)))
        return out

    def _path_order(self, comp: Component) -> List[int]:
        """The rows of a path component, from the end of its first crease."""
        if not comp.rows:
            return []
        adj: Dict[Tuple[int, int], List[int]] = {}
        for ri in comp.rows:
            for a, b in self.rows[ri].terms:
                adj.setdefault((min(a, b), max(a, b)), []).append(ri)
        cur = self.adjacent_pair(comp.creases[0])
        order, used = [], set()
        while True:
            nxt = [ri for ri in adj.get(cur, []) if ri not in used]
            if not nxt:
                break
            ri = nxt[0]
            used.add(ri)
            order.append(ri)
            u, w = [(min(a, b), max(a, b)) for a, b in self.rows[ri].terms]
            cur = w if u == cur else u
        return order

    @cached_property
    def cycles(self) -> int:
        """The number of cycles of the row graph (components with no crease)."""
        return sum(1 for c in self.components if not c.creases and c.rows)

    def rank(self) -> int:
        """The rank of the rows (Proposition 2: ``N - m - c`` without TC rows)."""
        return self.layer_system().solve().rank

    def persistence_pairs(self) -> Optional[List[Tuple[int, int]]]:
        """Persistence pairs of the walk, read as a height on the circle.

        Each pair is ``(minimum, maximum)``; the essential pair, of the lowest
        and the highest crease, comes last.  Theorem 3: at a vertex without
        taco--taco rows these are the pairs of Theorem 2.  Returns ``None``
        when two creases of the same type share a ray (the elder rule would
        meet a tie).
        """
        if self.has_tc:
            return None
        n, pos = self.n, self.pos
        order = sorted(range(n), key=lambda k: (pos[k], self.is_max(k)))
        parent: Dict[int, int] = {}
        oldest: Dict[int, int] = {}

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        out, essential = [], None
        for k in order:
            if not self.is_max(k):
                parent[k] = k
                oldest[k] = k
                continue
            a, b = find((k - 1) % n), find((k + 1) % n)
            parent[k] = a
            if a == b:
                essential = (oldest[a], k)
                continue
            ma, mb = oldest[a], oldest[b]
            old, young = (ma, mb) if pos[ma] < pos[mb] else (mb, ma)
            out.append((young, k))
            parent[b] = a
            oldest[a] = old
        out.sort(key=lambda p: (pos[p[1]] - pos[p[0]], p))
        return out + [essential]

    def nested(self) -> bool:
        """Proposition 1: the pairs, drawn as chords, do not cross."""
        chords = [tuple(sorted(p.creases)) for p in (self.pairs or [])]
        for (a, b), (c, d) in combinations(chords, 2):
            if a < c < b < d or c < a < d < b:
                return False
        return True

    def big_little_big(self) -> List[Tuple[int, int, int, Tuple[int, int]]]:
        """Proposition 4: sectors smaller than both neighbours.

        Returns ``(sector, crease_before, crease_after, (row, row))``: the two
        creases are forced opposite by the two rows.
        """
        out = []
        index = {(r.kind, r.creases, r.tortilla): i for i, r in enumerate(self.rows)}
        for i in range(self.n):
            L = self.length(i)
            if L < self.length(i - 1) and L < self.length(self.nxt(i)):
                k0, k1 = (i - 1) % self.n, i
                r1 = index[("TT", (k0,), self.nxt(i))]
                r2 = index[("TT", (k1,), (i - 1) % self.n)]
                out.append((i, k0, k1, (r1, r2)))
        return out

    # ----------------------------------------------------- Theorem 4, Hull
    @cached_property
    def hull(self) -> HullRecursion:
        """Hull's crimping recursion on the walk (Sec. 7)."""
        return hull_recursion(self.pos)

    @property
    def E(self) -> int:
        return self.hull.E

    @property
    def wflat_count(self) -> int:
        """``|W_flat(v)|``, by Hull's count."""
        return self.hull.flat_count

    def theorem4_holds(self) -> bool:
        """Theorem 4: the components are the blocks, with the same parities,
        and ``gamma = E + 1``."""
        mine = sorted((tuple(sorted(r.creases)), r.parity) for r in self.relations)
        hulls = sorted((tuple(sorted(b.creases)), b.valley_parity)
                       for b in self.hull.blocks)
        return mine == hulls and self.gamma == self.E + 1

    def verify_theorems(self) -> None:
        """Raise :class:`InternalError` if a theorem of the paper fails here.

        Every check compares two independent computations, so a failure would
        mean a bug, or a counterexample.
        """
        mult = self.pair_multiplicities()
        adj = {self.adjacent_pair(k) for k in range(self.n)}
        if self.n >= 4 and any(mult[p] != (1 if p in adj else 2) for p in mult):
            raise InternalError("Lemma 2 fails")
        if not self.theorem1_holds() or not self.gauge_homogeneous():
            raise InternalError("Theorem 1 fails")
        if not self.theorem4_holds():
            raise InternalError("Theorem 4 fails")
        if not self.has_tc:
            T, B = self.top[0], self.bottom[0]
            eq = [p for p in self.pairs if p.equal]
            if len(self.pairs) != self.m or len(eq) != 1 or set(eq[0].creases) != {T, B}:
                raise InternalError("Theorem 2 fails")
            pers = {frozenset(p) for p in self.persistence_pairs()}
            if pers != {frozenset(p.creases) for p in self.pairs}:
                raise InternalError("Theorem 3 fails")
            if not self.nested():
                raise InternalError("Proposition 1 fails")

    # ----------------------------------------------------------- checking
    def check(self, word) -> AssignmentCheck:
        """Test a mountain--valley assignment against the linear constraints.

        ``word`` is a string such as ``"MMMMVV"`` (crease ``e1`` first) or a
        sequence of ``+1`` (mountain) / ``-1`` (valley).
        """
        sigma = parse_assignment(word, self.n)
        bits = [0 if s > 0 else 1 for s in sigma]
        mv = sum(sigma)
        violated = [c for c in self.components
                    if c.relation is not None and not c.relation.holds(bits)]
        ok, fail = self.hull.test(sigma)
        blb = [(i, k0, k1) for i, k0, k1, _ in self.big_little_big()
               if sigma[k0] == sigma[k1]]
        return AssignmentCheck(sigma=sigma, mv=mv, maekawa_mod4=(mv % 4 == 2),
                               maekawa=mv in (2, -2), violated=violated,
                               in_wlin=not violated, flat_foldable=ok,
                               hull_failure=fail, big_little_big=blb)

    def wlin_words(self) -> List[Tuple[int, ...]]:
        """All assignments in ``W_lin(v)`` (use only for small degree)."""
        return [s for s in _all_words(self.n)
                if all(r.holds([0 if x > 0 else 1 for x in s]) for r in self.relations)]

    def wflat_words(self) -> List[Tuple[int, ...]]:
        """All flat-foldable assignments, by Hull's recursion (small degree)."""
        return [s for s in _all_words(self.n) if self.hull.test(s)[0]]

    # ------------------------------------------------------------ naming
    def cname(self, k: int) -> str:
        if k >= self.n:              # an e* of the recursion
            return f"e*{k - self.n + 1}"
        return self.crease_names[k]

    def fname(self, i: int) -> str:
        return self.sector_names[i]

    def describe_row(self, r: Row) -> str:
        return r.describe(self.cname, self.fname)

    def describe_relation(self, rel: Relation) -> str:
        names = ", ".join(self.cname(k) for k in rel.creases)
        if rel.is_pair:
            return f"{names}: {'equal' if rel.equal else 'opposite'}"
        word = "even" if rel.parity == 0 else "odd"
        return f"{{{names}}}: {word} number of valleys (M - V = {rel.mv_mod4} mod 4)"


def _all_words(n: int):
    for code in range(1 << n):
        yield tuple(-1 if (code >> k) & 1 else 1 for k in range(n))
