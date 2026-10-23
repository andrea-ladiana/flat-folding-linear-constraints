"""The theorems of the paper, checked on random vertices.

Each test compares two computations that the paper proves equal and that the
code obtains independently: the hypergraph of the rows against Gaussian
elimination, the relations against the enumeration of all layer orders,
Hull's recursion against both.
"""

import os
import random

import pytest

from linfold import Vertex
from linfold.vertex import _all_words
from helpers import affine_span, generic_angles, lattice_angles, layer_orders

STEPS = [10, 12, 15, 18, 20, 30, 36, 45, 60]
#: multiply the number of random vertices, e.g. LINFOLD_TEST_SCALE=20
SCALE = max(1, int(os.environ.get("LINFOLD_TEST_SCALE", "1")))


def lattice_vertices(count, degrees, seed):
    rng = random.Random(seed)
    seen, out = set(), []
    while len(out) < count:
        n = rng.choice(degrees)
        a = lattice_angles(n, rng.choice(STEPS), rng)
        if a is None:
            continue
        key = min(tuple(a[i:] + a[:i]) for i in range(n))
        if key in seen:
            continue
        seen.add(key)
        out.append(a)
    return out


def generic_vertices(count, degrees, seed):
    rng = random.Random(seed)
    return [generic_angles(rng.choice(degrees), rng) for _ in range(count)]


@pytest.mark.parametrize("angles", generic_vertices(150 * SCALE, [4, 6, 8, 10, 12, 16, 20], 1)
                         + lattice_vertices(250 * SCALE, [4, 6, 8, 10, 12], 2))
def test_theorems_hold(angles):
    """Lemma 2, Theorem 1 (both forms), Theorems 2-4, Propositions 1-2."""
    v = Vertex(angles)
    v.verify_theorems()           # raises on any failure
    if not v.has_tc:
        N = len(v.overlapping_pairs)
        assert v.rank() == N - v.m - v.cycles               # Proposition 2


@pytest.mark.parametrize("angles", lattice_vertices(120 * SCALE, [4, 6, 8, 10], 3))
def test_lemma3_against_elimination(angles):
    """The components give the projection of the solution space (Lemma 3)."""
    v = Vertex(angles)
    sysm = v.layer_system()
    sol = sysm.solve()
    assert sol.consistent
    cols = [sysm.column(v.adjacent_pair(k)) for k in range(v.n)]
    assert sol.projection_rank(cols) == v.dim_wlin
    # a particular solution induces an assignment satisfying every relation
    x = sol.particular()
    bits = []
    for k in range(v.n):
        a, b = k, (k + 1) % v.n
        val = x[sysm.column((min(a, b), max(a, b)))] ^ int(a > b)
        bits.append(val ^ int(v.parity[k] < 0))
    assert all(r.holds(bits) for r in v.relations)


@pytest.mark.parametrize("angles", lattice_vertices(min(160 * SCALE, 700), [4, 6], 4)
                         + lattice_vertices(12 * SCALE, [8], 5)
                         + generic_vertices(30 * SCALE, [4, 6], 6))
def test_hull_and_affine_hull_against_layer_orders(angles):
    """W_flat from all layer orders = Hull's recursion; W_lin = its affine
    hull (Theorem 4); Corollary 2 decides when they coincide."""
    v = Vertex(angles)
    flat, _ = layer_orders(v)
    assert flat == set(v.wflat_words())
    assert len(flat) == v.wflat_count
    lin = set(v.wlin_words())
    assert lin == affine_span(flat)
    assert (lin == flat) == v.hull.linear_equals_flat


@pytest.mark.parametrize("angles", lattice_vertices(60 * SCALE, [4, 6, 8], 7))
def test_w4_test_matches_relations(angles):
    """Hull's recursion read modulo four is membership in W_lin."""
    v = Vertex(angles)
    lin = set(v.wlin_words())
    for s in _all_words(v.n):
        assert v.hull.test(s, mod4=True)[0] == (s in lin)


def test_persistence_with_shared_rays():
    """Theorem 3 at degenerate vertices without taco-taco rows."""
    rng = random.Random(8)
    tested = 0
    while tested < 150:
        a = lattice_angles(rng.choice([4, 6, 8, 10]), rng.choice([10, 15, 20, 30]), rng)
        if a is None:
            continue
        v = Vertex(a)
        if v.has_tc or v.generic:
            continue
        tested += 1
        pers = {frozenset(p) for p in v.persistence_pairs()}
        assert pers == {frozenset(p.creases) for p in v.pairs}


def test_float_angles_with_tolerance():
    """Floats close to exact angles give the exact combinatorics."""
    exact = Vertex([45, 135, 135, 45])
    noisy = Vertex([45 + 1e-9, 135 - 2e-9, 135 + 1e-9, 45], tol=1e-6)
    assert [r.kind for r in noisy.rows] == [r.kind for r in exact.rows]
    assert noisy.wlin_count == exact.wlin_count and noisy.wflat_count == exact.wflat_count


def test_cone_walk():
    """Walks whose angles do not add up to 360 (vertices of cones)."""
    v = Vertex([10, 30, 50, 30])          # alternating sum 0, total 120
    v.verify_theorems()
    assert v.wlin_count == 2 ** v.dim_wlin


def test_errors():
    from linfold import VertexError
    with pytest.raises(VertexError):
        Vertex([90, 90, 90])               # odd degree
    with pytest.raises(VertexError):
        Vertex([100, 90, 80, 91])          # Kawasaki fails
    with pytest.raises(VertexError):
        Vertex([0, 180, 0, 180])
