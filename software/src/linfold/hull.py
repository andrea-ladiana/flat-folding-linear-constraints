"""Hull's crimping recursion, exact and modulo four (Sec. 7 of the paper).

A closed walk is given by the positions of its creases in the folded image,
read cyclically; the sector between two consecutive creases has as angle the
distance between their positions.  While the angles are not all equal, a
maximal run of ``k + 1`` consecutive sectors of smallest angle is *crimped*:

* ``k`` even: the run and its two neighbours merge into one sector, and the
  ``k + 2`` creases of the run disappear; they form a **block**, on which every
  flat-foldable assignment has ``M - V = 0``;
* ``k`` odd: the run disappears, and its ``k + 2`` creases are replaced by one
  crease ``e*`` at the same position; they fold as ``e*``, with
  ``M - V = sigma(e*)``.

The creases of the final walk, with all angles equal, form the last block, on
which ``M - V = +-2``.  Hull proved that these conditions describe exactly the
flat-foldable assignments of a single vertex [Hull 2003, Thms. 3--5].  Read
modulo four, they describe the affine hull over F2 of that set (Theorem 4 of
the paper), which the linear constraints compute.

Crease labels are integers ``0 .. n-1``; the creases ``e*`` created by odd
crimps receive the labels ``n, n+1, ...``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from math import comb
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

__all__ = ["Crimp", "Block", "HullRecursion", "hull_recursion"]


@dataclass(frozen=True)
class Crimp:
    """One step of the recursion."""

    k: int                          #: the run has k + 1 sectors
    creases: Tuple[int, ...]        #: the k + 2 creases of the run (labels)
    star: Optional[int]             #: the label of e* when k is odd
    angle: object                   #: the smallest angle crimped

    @property
    def even(self) -> bool:
        return self.k % 2 == 0


@dataclass(frozen=True)
class Block:
    """A set of creases that the recursion treats together.

    Every flat-foldable assignment has ``M - V = target`` on the block when
    ``final`` is false (``target = 0``), and ``M - V = +-2`` when it is the
    final block.  Modulo four this is a parity condition on the number of
    valleys: ``V = valley_parity (mod 2)``.
    """

    creases: FrozenSet[int]
    final: bool

    @property
    def valley_parity(self) -> int:
        L = len(self.creases)
        return ((L - 2) // 2 if self.final else L // 2) % 2


@dataclass
class HullRecursion:
    n: int
    crimps: List[Crimp]
    final: Tuple[int, ...]
    blocks: List[Block]
    expand: Dict[int, FrozenSet[int]] = field(repr=False)

    @property
    def E(self) -> int:
        """The number of crimps with ``k`` even."""
        return sum(1 for c in self.crimps if c.even)

    @property
    def dim_w4(self) -> int:
        """``n - 1 - E``, the dimension of ``W_4(v)`` (Theorem 4)."""
        return self.n - 1 - self.E

    @property
    def flat_count(self) -> int:
        """Hull's count of flat-foldable assignments [Hull 2003]."""
        total = 1
        for c in self.crimps:
            L = c.k + 2
            total *= comb(L, L // 2) if c.even else comb(L, (c.k + 1) // 2)
        d = len(self.final)
        total *= 2 * comb(d, d // 2 - 1) if d >= 2 else 1
        return total

    @property
    def linear_equals_flat(self) -> bool:
        """Corollary 2: ``W_lin = W_flat`` iff every run is a single sector
        and the recursion ends at degree two or four."""
        return all(c.k == 0 for c in self.crimps) and len(self.final) in (2, 4)

    # ---------------------------------------------------------------- tests
    def test(self, sigma: Sequence[int], mod4: bool = False):
        """Run the recursion on an assignment (``+1`` mountain, ``-1`` valley).

        Returns ``(ok, step)``: ``step`` is ``None`` on success, otherwise a
        dict describing the first condition that fails.  With ``mod4=False``
        this is Hull's characterisation of flat-foldable assignments; with
        ``mod4=True`` it decides membership in ``W_4(v)``.
        """
        val: Dict[int, int] = {k: int(s) for k, s in enumerate(sigma)}
        for i, c in enumerate(self.crimps):
            s = sum(val[e] for e in c.creases)
            if c.even:
                good = (s % 4 == 0) if mod4 else (s == 0)
                if not good:
                    return False, dict(step=i, crimp=c, sum=s,
                                       need="0 (mod 4)" if mod4 else "0")
            else:
                if mod4:
                    val[c.star] = 1 if s % 4 == 1 else -1
                else:
                    if s not in (1, -1):
                        return False, dict(step=i, crimp=c, sum=s, need="+1 or -1")
                    val[c.star] = s
        s = sum(val[e] for e in self.final)
        good = (s % 4 == 2) if mod4 else (s in (2, -2))
        if not good:
            return False, dict(step=len(self.crimps), crimp=None, sum=s,
                               need="2 (mod 4)" if mod4 else "+2 or -2")
        return True, None


def hull_recursion(positions: Sequence) -> HullRecursion:
    """Run the crimping recursion on a closed walk.

    ``positions[i]`` is the position of crease ``i``; the sector between
    creases ``i - 1`` and ``i`` has angle ``|positions[i] - positions[i-1]|``.
    Equal angles are recognised by exact equality, so positions should be
    exact numbers or values already snapped to a tolerance (as
    :class:`linfold.vertex.Vertex` does): two consecutive sectors have equal
    angles exactly when their outer creases have equal positions.
    """
    n = len(positions)
    pos: Dict[int, object] = {k: positions[k] for k in range(n)}
    walk: List[int] = list(range(n))           # cyclic list of crease labels
    expand: Dict[int, FrozenSet[int]] = {k: frozenset([k]) for k in range(n)}
    crimps: List[Crimp] = []
    blocks: List[Block] = []
    fresh = n

    def angle(i: int):
        L = len(walk)
        return abs(pos[walk[i % L]] - pos[walk[(i - 1) % L]])

    while True:
        L = len(walk)
        angles = [angle(i) for i in range(L)]
        lo = min(angles)
        if all(a == lo for a in angles):
            break
        # the start of a maximal run of smallest sectors
        i = next(j for j in range(L) if angles[j] == lo and angles[j - 1] != lo)
        k = 0
        while angles[(i + k + 1) % L] == lo:
            k += 1
        run = [walk[(i - 1 + t) % L] for t in range(k + 2)]   # k + 2 creases
        drop = {(i - 1 + t) % L for t in range(k + 2)}
        if k % 2 == 0:
            blocks.append(Block(frozenset().union(*(expand[e] for e in run)), False))
            crimps.append(Crimp(k, tuple(run), None, lo))
            walk = [walk[j] for j in range(L) if j not in drop]
        else:
            star = fresh
            fresh += 1
            pos[star] = pos[run[0]]
            expand[star] = frozenset().union(*(expand[e] for e in run))
            crimps.append(Crimp(k, tuple(run), star, lo))
            first = (i - 1) % L
            walk = [star if j == first else walk[j]
                    for j in range(L) if j == first or j not in drop]
    final = tuple(walk)
    blocks.append(Block(frozenset().union(*(expand[e] for e in final)), True))
    return HullRecursion(n=n, crimps=crimps, final=final, blocks=blocks, expand=expand)
