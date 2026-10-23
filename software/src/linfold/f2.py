"""Affine linear algebra over the field with two elements.

Every constraint handled by :mod:`linfold` is an affine equation over
:math:`\\mathbb{F}_2`,

.. math::  x_{c_1} + x_{c_2} + \\dots + x_{c_r} = b ,

and this module solves systems of them.  A row is stored as a Python integer
used as a bit set over the columns, so that adding two rows is a single
``^``.  Besides rank and consistency, a :class:`Solution` answers the three
questions the paper asks of a linear system:

* is it **consistent**?  If not, :meth:`Solution.certificate` returns a set of
  input rows whose left-hand sides cancel and whose constants add up to one,
  the certificate of Corollary 4 of the paper, reduced to an inclusion-minimal
  set;
* which variables are **forced**, that is, take the same value in every
  solution (:meth:`Solution.form`);
* what is the **dimension of the projection** of the solution space onto a set
  of columns (:meth:`Solution.projection_rank`), which is how the
  mountain-valley assignments induced by the solutions are counted.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Hashable, Iterable, List, Optional, Sequence, Tuple

__all__ = ["AffineSystem", "Solution", "Form", "mask_of", "bits"]


def mask_of(columns: Iterable[int]) -> int:
    """The bit set of a list of columns; a repeated column cancels."""
    m = 0
    for c in columns:
        m ^= 1 << int(c)
    return m


def bits(mask: int) -> List[int]:
    """The columns of a bit set, in increasing order."""
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


@dataclass(frozen=True)
class Form:
    """An affine form ``const + sum of the free variables in free_mask``.

    The free variables are numbered by their position in
    :attr:`Solution.free`.  A form with ``free_mask == 0`` is constant on the
    solution space: the quantity it describes is forced.
    """

    const: int
    free_mask: int

    @property
    def forced(self) -> bool:
        return self.free_mask == 0

    def __add__(self, other: "Form") -> "Form":
        return Form(self.const ^ other.const, self.free_mask ^ other.free_mask)


@dataclass
class Solution:
    """The result of :meth:`AffineSystem.solve`."""

    n_vars: int
    n_rows: int
    rank: int
    consistent: bool
    #: pivot column -> (row mask, rhs); every pivot row has its pivot as its
    #: lowest column
    pivot_rows: Dict[int, Tuple[int, int]] = field(default_factory=dict)
    free: List[int] = field(default_factory=list)
    #: index (in input order) of the first row found inconsistent, or -1
    first_conflict: int = -1
    _system: Any = None
    _forms: Dict[int, Form] = field(default_factory=dict, repr=False)

    @property
    def nullity(self) -> int:
        return self.n_vars - self.rank

    @property
    def log2_solutions(self) -> Optional[int]:
        """``log2`` of the number of solutions, ``None`` if there are none."""
        return self.nullity if self.consistent else None

    # -------------------------------------------------------------- forms
    def form(self, column: int) -> Form:
        """The value of a variable as an affine form in the free variables."""
        if not self.consistent:
            raise ValueError("an inconsistent system has no solution")
        hit = self._forms.get(column)
        if hit is not None:
            return hit
        free_index = {c: i for i, c in enumerate(self.free)}
        # iterative evaluation in decreasing column order: a pivot row only
        # involves columns larger than its pivot
        stack = [column]
        while stack:
            c = stack[-1]
            if c in self._forms:
                stack.pop()
                continue
            if c in free_index:
                self._forms[c] = Form(0, 1 << free_index[c])
                stack.pop()
                continue
            if c not in self.pivot_rows:          # a column in no row at all
                raise KeyError(c)
            mask, b = self.pivot_rows[c]
            rest = bits(mask ^ (1 << c))
            missing = [d for d in rest if d not in self._forms]
            if missing:
                stack.extend(missing)
                continue
            f = Form(b, 0)
            for d in rest:
                f = f + self._forms[d]
            self._forms[c] = f
            stack.pop()
        return self._forms[column]

    def sum_form(self, columns: Iterable[int], const: int = 0) -> Form:
        """The affine form of ``const + sum of the given variables``."""
        f = Form(const & 1, 0)
        for c in columns:
            f = f + self.form(c)
        return f

    def projection_rank(self, columns: Sequence[int]) -> int:
        """Dimension of the image of the solution space on ``columns``."""
        basis: Dict[int, int] = {}
        for c in columns:
            m = self.form(c).free_mask
            while m:
                hb = m.bit_length() - 1
                if hb not in basis:
                    basis[hb] = m
                    break
                m ^= basis[hb]
        return len(basis)

    def particular(self) -> List[int]:
        """One solution (every free variable set to zero)."""
        return [self.form(c).const for c in range(self.n_vars)]

    # -------------------------------------------------------- certificate
    def certificate(self, minimise: bool = True, limit: int = 4000) -> List[int]:
        """Input rows whose left-hand sides cancel and whose constants sum to 1.

        The set is found by eliminating again with provenance tracking, on the
        rows up to the first conflict only, and is then reduced to an
        inclusion-minimal set by deleting rows one at a time (when it has at
        most ``limit`` rows).  Returns the row indices in increasing order.
        """
        if self.consistent:
            raise ValueError("a consistent system has no certificate")
        sysm = self._system
        upto = self.first_conflict + 1
        cert = sysm._certificate_among(list(range(upto)))
        if minimise and len(cert) <= limit:
            cert = sysm._minimise(cert)
        return sorted(cert)


class AffineSystem:
    """A system of affine equations over F2.

    Columns (variables) may be registered by name with :meth:`var`, or used
    as plain integers.  Every row carries an arbitrary ``tag`` (its
    provenance), which certificates refer back to.
    """

    def __init__(self, n_vars: int = 0):
        self.n_vars = n_vars
        self.rows: List[int] = []
        self.rhs: List[int] = []
        self.tags: List[Any] = []
        self._names: Dict[Hashable, int] = {}
        self.names: List[Hashable] = [None] * n_vars

    # ----------------------------------------------------------- building
    def var(self, name: Hashable) -> int:
        """The column of a named variable, created on first use."""
        c = self._names.get(name)
        if c is None:
            c = self.n_vars
            self.n_vars += 1
            self._names[name] = c
            self.names.append(name)
        return c

    def has_var(self, name: Hashable) -> bool:
        return name in self._names

    def column(self, name: Hashable) -> int:
        return self._names[name]

    def add(self, columns: Iterable[int], rhs: int, tag: Any = None) -> int:
        """Add the row ``sum(x[c] for c in columns) = rhs``; returns its index."""
        m = mask_of(columns)
        top = m.bit_length()
        if top > self.n_vars:
            self.n_vars = top
            self.names.extend([None] * (top - len(self.names)))
        self.rows.append(m)
        self.rhs.append(int(rhs) & 1)
        self.tags.append(tag)
        return len(self.rows) - 1

    def __len__(self) -> int:
        return len(self.rows)

    def subsystem(self, indices: Sequence[int]) -> "AffineSystem":
        out = AffineSystem(self.n_vars)
        out.names = list(self.names)
        out._names = dict(self._names)
        for i in indices:
            out.rows.append(self.rows[i])
            out.rhs.append(self.rhs[i])
            out.tags.append(self.tags[i])
        return out

    # ------------------------------------------------------------ solving
    def solve(self) -> Solution:
        """Gaussian elimination; rank, consistency, free variables."""
        piv: Dict[int, Tuple[int, int]] = {}
        first_conflict = -1
        for k, (m, b) in enumerate(zip(self.rows, self.rhs)):
            while m:
                c = (m & -m).bit_length() - 1
                hit = piv.get(c)
                if hit is None:
                    piv[c] = (m, b)
                    break
                m ^= hit[0]
                b ^= hit[1]
            else:
                if b and first_conflict < 0:
                    first_conflict = k
        free = [c for c in range(self.n_vars) if c not in piv]
        return Solution(n_vars=self.n_vars, n_rows=len(self.rows),
                        rank=len(piv), consistent=first_conflict < 0,
                        pivot_rows=piv, free=free,
                        first_conflict=first_conflict, _system=self)

    def is_consistent(self, indices: Optional[Sequence[int]] = None) -> bool:
        idx = range(len(self.rows)) if indices is None else indices
        piv: Dict[int, Tuple[int, int]] = {}
        for k in idx:
            m, b = self.rows[k], self.rhs[k]
            while m:
                c = (m & -m).bit_length() - 1
                hit = piv.get(c)
                if hit is None:
                    piv[c] = (m, b)
                    break
                m ^= hit[0]
                b ^= hit[1]
            else:
                if b:
                    return False
        return True

    # ------------------------------------------------------- certificates
    def _certificate_among(self, indices: Sequence[int]) -> List[int]:
        """Rows among ``indices`` that add up to ``0 = 1`` (empty if none)."""
        piv: Dict[int, Tuple[int, int, int]] = {}
        for pos, k in enumerate(indices):
            m, b, o = self.rows[k], self.rhs[k], 1 << pos
            while m:
                c = (m & -m).bit_length() - 1
                hit = piv.get(c)
                if hit is None:
                    piv[c] = (m, b, o)
                    break
                m ^= hit[0]
                b ^= hit[1]
                o ^= hit[2]
            else:
                if b:
                    return [indices[i] for i in bits(o)]
        return []

    def _minimise(self, cert: List[int]) -> List[int]:
        """Delete rows from a certificate while it stays a certificate."""
        cur = list(cert)
        i = 0
        while i < len(cur):
            trial = cur[:i] + cur[i + 1:]
            smaller = self._certificate_among(trial)
            if smaller:
                cur = smaller          # may drop more than one row at once
                i = 0 if len(smaller) < len(trial) else i
            else:
                i += 1
        return cur

    def check_certificate(self, indices: Sequence[int]) -> bool:
        """Do these rows have cancelling left-hand sides and constant 1?"""
        m, b = 0, 0
        for k in indices:
            m ^= self.rows[k]
            b ^= self.rhs[k]
        return m == 0 and b == 1
