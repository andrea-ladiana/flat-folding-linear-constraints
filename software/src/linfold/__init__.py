"""linfold: the linear constraints of flat folding.

A reference implementation of

    A. Ladiana, *Maekawa's theorem and the linear constraints of flat folding*.

The taco--tortilla and taco--taco constraints on the layer order of a flat
folding are linear over F2.  This package computes them, at a single vertex
from its angles and on a whole crease pattern from its folded polygons, and
reads off what the paper proves they say: the relations that pair up the
creases at every vertex, the blocks of Hull's recursion, the space of
mountain--valley assignments they allow, and, when they are inconsistent, a
short certificate that the pattern cannot fold flat.

Quick start::

    >>> from linfold import Vertex
    >>> v = Vertex([40, 70, 100, 60, 40, 50])
    >>> [(p.creases, p.equal) for p in v.pairs]
    [((0, 5), False), ((1, 2), True), ((3, 4), False)]

    >>> from linfold import load, analyze
    >>> report = analyze(load("pattern.fold"))          # doctest: +SKIP
    >>> report.verdict, report.certificate              # doctest: +SKIP
"""

__version__ = "0.1.0"

from .f2 import AffineSystem                                    # noqa: E402
from .vertex import Vertex, VertexError                         # noqa: E402
from .hull import hull_recursion                                # noqa: E402
from .pattern import CreasePattern, load, from_segments         # noqa: E402
from .analysis import analyze, Report                           # noqa: E402
from .certificate import Certificate, verify                    # noqa: E402

__all__ = ["__version__", "AffineSystem", "Vertex", "VertexError", "hull_recursion",
           "CreasePattern", "load", "from_segments", "analyze", "Report",
           "Certificate", "verify"]
