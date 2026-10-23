"""Crease patterns: the local rows against the folded polygons, and verdicts."""

import math
import os
import random

import pytest

from linfold import analyze, from_segments, load
from linfold import generators as gen
from linfold.rows import canonical
from helpers import EXAMPLES, lattice_angles


def key(r):
    return (r.kind, tuple(sorted(r.creases)), r.tortilla, canonical(r.terms))


def random_single_vertices(count, seed):
    rng = random.Random(seed)
    out = []
    while len(out) < count:
        a = lattice_angles(rng.choice([4, 6, 8]), rng.choice([10, 15, 20, 30, 45]), rng)
        if a is not None:
            out.append(a)
    return out


@pytest.mark.parametrize("angles", random_single_vertices(60, 11))
def test_rows_from_angles_equal_rows_from_polygons(angles):
    """At a single vertex every facet and crease is incident to the vertex, so
    the rows found from the folded polygons are exactly the rows of Lemma 1,
    which the vertex computes from the angles alone."""
    rot = random.Random(sum(angles)).uniform(0, 360)
    cp = from_segments(gen.single_vertex(angles), "v")
    assert len(cp.vertices) == 1 and not cp.fatal_issues
    pv = cp.vertices[0]
    local = {key(r) for r in cp.local_rows(pv)}
    glob = {key(r) for r in cp.folding.rows}
    assert local == glob
    rep = analyze(cp)
    assert rep.verdict == "passes" and not rep.warnings
    assert rep.local.mv_dim == rep.global_.mv_dim == pv.vertex.dim_wlin
    assert rep.global_.vertex_rows_redundant


def test_triangle_certificate_is_the_six_rows_of_the_paper():
    cp = from_segments(gen.triangle(), "triangle")
    assert len(cp.vertices) == 3 and not cp.issues
    rep = analyze(cp)
    assert rep.verdict == "not-flat-foldable"
    cert = rep.local.certificate
    assert cert.holds() and len(cert.items) == 6
    assert all(it.kind == "TT" for it in cert.items)
    # two rows at each corner, forming its big-little-big relation
    assert sorted(g.vertex for g in cert.groups) == [0, 1, 2]
    assert all(len(g.items) == 2 and g.parity == 1 for g in cert.groups)
    g = rep.global_
    assert not g.consistent and g.certificate.holds()
    assert g.vertex_rows_redundant


def test_triangle_with_larger_inner_angles_folds():
    """With 90 degrees inside, the inner sector is no longer smaller than both
    neighbours: no big-little-big relation, no obstruction."""
    cp = from_segments(gen.triangle((100, 80, 100, 80)), "triangle")
    rep = analyze(cp)
    assert rep.local.consistent


@pytest.mark.parametrize("name,verdict", [
    ("triangle.fold", "not-flat-foldable"),
    ("kawasaki_violated.fold", "not-flat-foldable"),
    ("vertex_example1.fold", "passes"),
    ("vertex_example1.opx", "passes"),
    ("vertex_degree16_wrong_labels.fold", "labels-not-flat-foldable"),
    ("vertex_45_135_135_45.fold", "labels-not-flat-foldable"),
    ("vertex_regular6.fold", "passes"),
    ("miura_6x6.fold", "passes"),
    ("map_3x3.fold", "passes"),
    ("waterbomb_base.cp", "passes"),
    ("preliminary_base.svg", "passes"),
])
def test_example_files(name, verdict):
    rep = analyze(load(os.path.join(EXAMPLES, name)))
    assert rep.verdict == verdict
    assert not rep.warnings


def test_degree16_labels_local_certificate():
    rep = analyze(load(os.path.join(EXAMPLES, "vertex_degree16_wrong_labels.fold")))
    v = rep.vertices[0]
    assert v.maekawa and not v.in_wlin and not v.flat_foldable
    cert = rep.local.labels_certificate
    assert cert.holds()
    assert sum(it.kind == "assignment" for it in cert.items) == 2


def test_example3_passes_linear_filters_but_not_hull():
    """VMVV satisfies every linear constraint; only Hull's recursion
    (transitivity) rejects it."""
    rep = analyze(load(os.path.join(EXAMPLES, "vertex_45_135_135_45.fold")))
    assert rep.local.labels_consistent and rep.global_.labels_consistent
    assert rep.vertices[0].in_wlin and rep.vertices[0].flat_foldable is False
    assert rep.certificate is None


def test_map_rank_matches_reference():
    """The 3x3 map: rank 12 of the affine system (OrigamiAnalyzer's
    reference value, holonomy rows included, equal by Corollary 4)."""
    rep = analyze(load(os.path.join(EXAMPLES, "map_3x3.fold")))
    assert rep.global_.rank == 12 and rep.global_.variables == 36


def test_forced_labels_propagate():
    """Labelling one crease of a degree-four vertex forces its partners."""
    segs = gen.single_vertex([60, 100, 120, 80], "MUUU")
    rep = analyze(from_segments(segs, "v"))
    # e1 = M; the big-little-big pair of the 60-degree sector is (e4, e1),
    # so e4 = V; the other pair (e2, e3) is forced equal but not fixed
    cp = rep.cp
    v = cp.vertices[0]
    assert len(rep.local.forced) == 1
    (c, lab), = rep.local.forced.items()
    assert lab == "V"


def test_rotation_and_scale_invariance():
    angles = [40, 70, 100, 60, 40, 50]
    base = analyze(from_segments(gen.single_vertex(angles), "v"))
    th = math.radians(17.0)
    segs = [((1000 * (p[0] * math.cos(th) - p[1] * math.sin(th)) + 3,
              1000 * (p[0] * math.sin(th) + p[1] * math.cos(th)) - 7),
             (1000 * (q[0] * math.cos(th) - q[1] * math.sin(th)) + 3,
              1000 * (q[0] * math.sin(th) + q[1] * math.cos(th)) - 7), a)
            for p, q, a in gen.single_vertex(angles)]
    moved = analyze(from_segments(segs, "v"))
    assert moved.global_.rank == base.global_.rank
    assert moved.global_.rows == base.global_.rows
    assert moved.local.mv_dim == base.local.mv_dim


def test_odd_degree_and_dangling_crease():
    segs = gen._square(1.0) + [((0, 0), (1, 0), "U"), ((0, 0), (-1, 0.5), "U"),
                               ((0, 0), (-1, -0.5), "U")]
    rep = analyze(from_segments(segs, "odd"))
    assert rep.verdict == "not-flat-foldable"
    assert any(i.kind == "odd-degree" for i in rep.issues)
    segs = gen._square(1.0) + [((0, 0), (1, 0), "M"), ((-1, 0), (0.2, 0), "M"),
                               ((0.5, -1), (0.5, 0.3), "V")]
    rep = analyze(from_segments(segs, "dangling"))
    assert any(i.kind == "dangling-crease" for i in rep.issues)
