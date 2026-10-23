"""Shared helpers for the tests: random walks and brute-force layer orders."""

from __future__ import annotations

import itertools
import os
import random
from fractions import Fraction
from typing import List, Optional, Sequence, Set, Tuple

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "examples")


def composition(total: int, parts: int, rng: random.Random) -> List[int]:
    """A random composition of ``total`` into ``parts`` positive integers."""
    cuts = sorted(rng.sample(range(1, total), parts - 1))
    return [b - a for a, b in zip([0] + cuts, cuts + [total])]


def lattice_angles(n: int, step: int, rng: random.Random) -> Optional[List[int]]:
    """Angles that are multiples of ``step`` degrees, odd and even ones adding
    up to 180 (so that Kawasaki's condition holds and coincidences are exact)."""
    T = 180 // step
    if T < n // 2:
        return None
    odd, even = composition(T, n // 2, rng), composition(T, n // 2, rng)
    return [step * x for pair in zip(odd, even) for x in pair]


def generic_angles(n: int, rng: random.Random, denominator: int = 10 ** 6) -> List[Fraction]:
    """Random rational angles, generic with overwhelming probability."""
    T = 180 * denominator
    odd, even = composition(T, n // 2, rng), composition(T, n // 2, rng)
    return [Fraction(x, denominator) for pair in zip(odd, even) for x in pair]


def layer_orders(v) -> Tuple[Set[Tuple[int, ...]], int]:
    """All layer orders of a vertex satisfying its rows (transitivity holds
    for an order).  Returns the induced assignments and the number of orders."""
    n = v.n
    words: Set[Tuple[int, ...]] = set()
    count = 0
    eqs = [r.terms for r in v.rows]
    for order in itertools.permutations(range(n)):
        pos = [0] * n
        for depth, f in enumerate(order):
            pos[f] = depth
        if all(sum(pos[a] > pos[b] for a, b in terms) % 2 == 0 for terms in eqs):
            count += 1
            words.add(tuple(v.parity[k] * (1 if pos[k] < pos[(k + 1) % n] else -1)
                            for k in range(n)))
    return words, count


def affine_span(words) -> Set[Tuple[int, ...]]:
    """The affine span over F2 of a set of +-1 words."""
    words = list(words)
    n = len(words[0])
    enc = [sum(((1 - s) // 2) << i for i, s in enumerate(w)) for w in words]
    base = enc[0]
    basis = {}
    for w in enc[1:]:
        d = w ^ base
        while d:
            hb = d.bit_length() - 1
            if hb not in basis:
                basis[hb] = d
                break
            d ^= basis[hb]
    out = set()
    vecs = list(basis.values())
    for mask in range(1 << len(vecs)):
        s = base
        for i, b in enumerate(vecs):
            if mask >> i & 1:
                s ^= b
        out.add(tuple(1 - 2 * ((s >> i) & 1) for i in range(n)))
    return out
