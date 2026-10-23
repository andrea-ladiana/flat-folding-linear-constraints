"""Every number that the paper states about its examples."""

from linfold import Vertex
from helpers import layer_orders


def names(v, ks):
    return {v.cname(k) for k in ks}


def test_example1_walk_and_rows():
    v = Vertex([40, 70, 100, 60, 40, 50])
    assert v.pos == [40, -30, 70, 10, 50, 0]
    assert v.generic
    tt = {(v.cname(r.creases[0]), v.fname(r.tortilla)) for r in v.rows}
    expected = {("e1", f"f{g}") for g in (3, 4, 5, 6)} | \
               {("e4", f"f{g}") for g in (1, 2, 3, 6)} | \
               {("e5", "f3"), ("e5", "f4"), ("e6", "f2"), ("e6", "f3")}
    assert tt == expected
    assert len(v.overlapping_pairs) == 15
    assert v.rank() == 11                              # hence 16 solutions


def test_example1_solutions_and_states():
    v = Vertex([40, 70, 100, 60, 40, 50])
    sysm = v.layer_system()
    sol = sysm.solve()
    assert sol.consistent and sol.nullity == 4         # 16 solutions
    words, count = layer_orders(v)
    assert count == 12                                 # 12 transitive solutions
    assert len(words) == 8


def test_example1_pairs_persistence_and_fig2_state():
    v = Vertex([40, 70, 100, 60, 40, 50])
    pairs = {frozenset(names(v, p.creases)): p.equal for p in v.pairs}
    assert pairs == {frozenset({"e2", "e3"}): True,
                     frozenset({"e4", "e5"}): False,
                     frozenset({"e6", "e1"}): False}
    assert v.cycles == 1
    # the path of the extreme creases: the four rows with tortilla f3
    ext = next(p for p in v.pairs if p.equal)
    assert {v.fname(v.rows[i].tortilla) for i in ext.rows} == {"f3"}
    assert len(ext.rows) == 4
    pers = [tuple(v.cname(k) for k in p) for p in v.persistence_pairs()]
    assert set(pers[:-1]) == {("e6", "e1"), ("e4", "e5")}
    assert pers[-1] == ("e2", "e3")                    # the essential pair
    chk = v.check("MMMMVV")                            # the state of Fig. 2
    assert chk.mv == 2 and chk.in_wlin and chk.flat_foldable


def test_example3_degree_four():
    v = Vertex([45, 135, 135, 45])
    kinds = sorted((r.kind, tuple(v.cname(k) for k in r.creases),
                    v.fname(r.tortilla) if r.tortilla is not None else None)
                   for r in v.rows)
    assert kinds == [("TC", ("e1", "e3"), None), ("TT", ("e4",), "f2"),
                     ("TT", ("e4",), "f3")]
    assert v.gamma == 1 and v.wlin_count == 8 and v.wflat_count == 6
    for word in ("VMVV", "MVMM"):
        c = v.check(word)
        assert c.maekawa and c.in_wlin and not c.flat_foldable
    words, _ = layer_orders(v)
    assert len(words) == 6


def test_example4_regular_vertex():
    v = Vertex([60] * 6)
    assert not v.tt_rows and len(v.tc_rows) == 6
    assert v.E == 0 and v.wlin_count == 32 and v.wflat_count == 30
    c = v.check("MMMMMM")
    assert c.in_wlin and not c.flat_foldable and c.mv == 6
    # the explicit cyclic solution of the paper: odd sectors above even ones,
    # f1 > f3 > f5 > f1 and f2 > f6 > f4 > f2  (">" = above, x = 0)
    above = {(0, 2), (2, 4), (4, 0), (1, 5), (5, 3), (3, 1)}
    above |= {(a, b) for a in (0, 2, 4) for b in (1, 3, 5)}
    x = lambda a, b: 0 if (a, b) in above else 1      # noqa: E731
    for r in v.rows:
        assert sum(x(a, b) for a, b in r.terms) % 2 == 0
    sigma = [v.parity[k] * (1 if x(k, (k + 1) % 6) == 0 else -1) for k in range(6)]
    assert sigma == [1] * 6
    assert v.theorem1_holds()


def test_figure3c_degree_sixteen():
    v = Vertex([39, 29, 19, 10, 6, 10, 45, 46, 26, 14, 8, 12, 27, 42, 10, 17])
    assert v.generic and len(v.pairs) == 8 and v.nested()
    v.verify_theorems()
    eq = [p for p in v.pairs if p.equal]
    assert len(eq) == 1 and set(eq[0].creases) == {v.top[0], v.bottom[0]}


def test_big_little_big_rows():
    v = Vertex([40, 70, 100, 60, 40, 50])
    blb = {(v.fname(i), v.cname(a), v.cname(b)) for i, a, b, _ in v.big_little_big()}
    assert blb == {("f1", "e6", "e1"), ("f5", "e4", "e5")}
