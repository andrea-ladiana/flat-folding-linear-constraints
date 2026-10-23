import itertools
import random

from linfold.f2 import AffineSystem, bits, mask_of


def brute(sysm):
    sols = []
    for x in itertools.product((0, 1), repeat=sysm.n_vars):
        if all(sum(x[c] for c in bits(m)) % 2 == b for m, b in zip(sysm.rows, sysm.rhs)):
            sols.append(x)
    return sols


def random_system(rng, n, r, width=3):
    s = AffineSystem(n)
    for _ in range(r):
        s.add(rng.sample(range(n), rng.randint(1, min(width, n))), rng.randint(0, 1))
    return s


def test_rank_forms_and_projection_against_brute_force():
    rng = random.Random(0)
    for _ in range(300):
        n = rng.randint(1, 8)
        s = random_system(rng, n, rng.randint(0, 10))
        sol = s.solve()
        sols = brute(s)
        assert sol.consistent == bool(sols)
        if not sols:
            cert = sol.certificate()
            assert s.check_certificate(cert)
            for i in range(len(cert)):          # inclusion-minimal
                assert s.is_consistent(cert[:i] + cert[i + 1:])
            continue
        assert len(sols) == 2 ** sol.nullity
        for c in range(n):
            vals = {x[c] for x in sols}
            assert sol.form(c).forced == (len(vals) == 1)
            if len(vals) == 1:
                assert sol.form(c).const == vals.pop()
        cols = rng.sample(range(n), rng.randint(1, n))
        image = {tuple(x[c] for c in cols) for x in sols}
        assert len(image) == 2 ** sol.projection_rank(cols)
        p = sol.particular()
        assert tuple(p) in set(sols)


def test_repeated_columns_cancel():
    assert mask_of([1, 2, 1]) == 0b100
    s = AffineSystem(3)
    s.add([0, 0], 1)
    sol = s.solve()
    assert not sol.consistent and sol.certificate() == [0]


def test_named_variables():
    s = AffineSystem()
    a, b = s.var(("f1", "f2")), s.var(("f1", "f3"))
    assert s.var(("f1", "f2")) == a and s.n_vars == 2
    s.add([a, b], 0)
    s.add([a], 1)
    sol = s.solve()
    assert sol.form(b).forced and sol.form(b).const == 1
