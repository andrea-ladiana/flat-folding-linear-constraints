"""The linear constraints of a layer order, as data.

For two overlapping facets :math:`f_i, f_j` the layer variable is
:math:`x_{ij}\\in\\mathbb{F}_2`, with :math:`x_{ij}=0` when :math:`f_i` lies
above :math:`f_j` (the paper's :math:`r_{ij}=+1`) and :math:`x_{ji}=x_{ij}+1`.
Two families of constraints are linear (Sec. 2 of the paper):

``TT`` (taco--tortilla)
    if :math:`e_{ij}` is the crease between :math:`f_i, f_j` and the image of
    :math:`f_k` covers a segment of the image of :math:`e_{ij}` in its
    interior, then :math:`x_{ik} + x_{jk} = 0`;

``TC`` (taco--taco)
    if the images of the creases :math:`e_{ij}, e_{kl}` overlap in a segment
    and the four facets have a common region, then
    :math:`x_{ik} + x_{jk} + x_{il} + x_{jl} = 0`.

A :class:`Row` records the terms exactly as the definition writes them, with
the facets in the order given; :meth:`Row.equation` brings it to the canonical
orientation (smaller index first), which is where constants appear.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Hashable, Optional, Tuple

__all__ = ["Row", "canonical"]

Pair = Tuple[Hashable, Hashable]


def canonical(terms, key: Callable = lambda f: f):
    """Bring a sum of oriented layer variables to the canonical orientation.

    ``terms`` is a sequence of ordered pairs ``(a, b)``, each standing for
    ``x_ab``.  Returns ``(pairs, const)``: the unordered pairs that occur an
    odd number of times, each as ``(lo, hi)`` with ``key(lo) < key(hi)``, and
    the number of reversed terms modulo two, since ``x_ba = x_ab + 1``.
    """
    odd = {}
    const = 0
    for a, b in terms:
        if key(a) > key(b):
            a, b = b, a
            const ^= 1
        p = (a, b)
        if p in odd:
            del odd[p]
        else:
            odd[p] = True
    return tuple(sorted(odd, key=lambda p: (key(p[0]), key(p[1])))), const


@dataclass(frozen=True)
class Row:
    """One linear constraint ``sum of terms = 0``.

    Attributes
    ----------
    kind:
        ``"TT"`` or ``"TC"``.
    creases:
        the crease of a TT row, or the two creases of a TC row.
    tortilla:
        the covering facet of a TT row (``None`` for TC).
    terms:
        the oriented layer variables of the row, as ordered facet pairs.
    vertex:
        the vertex at which the row lies, when it lies at one.
    """

    kind: str
    creases: Tuple[Hashable, ...]
    tortilla: Optional[Hashable]
    terms: Tuple[Pair, ...]
    vertex: Optional[Hashable] = None

    def equation(self, key: Callable = lambda f: f):
        """``(pairs, const)``: the row as ``sum(x_p for p in pairs) = const``."""
        return canonical(self.terms, key)

    def describe(self, crease_name: Callable = str, facet_name: Callable = str) -> str:
        if self.kind == "TT":
            head = f"TT({crease_name(self.creases[0])}, {facet_name(self.tortilla)})"
        else:
            head = (f"TC({crease_name(self.creases[0])}, "
                    f"{crease_name(self.creases[1])})")
        body = " + ".join(f"x[{facet_name(a)},{facet_name(b)}]"
                          for a, b in self.terms)
        return f"{head}: {body} = 0"
