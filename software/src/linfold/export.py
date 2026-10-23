"""Export of the constraint system for other solvers.

``json``
    every layer variable (an overlapping pair of facets), every
    taco--tortilla and taco--taco row as an equation over F2, and every triple
    of facets with a common region (the transitivity constraints).

``xnf``
    the same system for a SAT solver with XOR clauses, such as CryptoMiniSat:
    the rows become XOR clauses (lines starting with ``x``) and transitivity
    becomes two ordinary clauses per triple.  For patterns with convex facets
    these constraints characterise the flat-folded states [Akitaya, Demaine
    and Ku], so the formula is satisfiable exactly when the pattern folds
    flat.  Assigned creases become unit clauses unless they are ignored.

Variable ``v`` (1-based) is the layer variable ``x_ab`` of the ``v``-th
overlapping pair ``a < b``: true when ``f_a`` lies *below* ``f_b``.
"""

from __future__ import annotations

from typing import Dict, List, Optional, TextIO

from .pattern import CreasePattern

__all__ = ["system_dict", "write_xnf"]


def _system(cp: CreasePattern, use_labels: bool):
    fo = cp.folding
    if not fo.ok:
        raise ValueError(fo.message)
    if cp.nonconvex_facets:
        raise ValueError("the pattern has non-convex facets")
    pairs = list(fo.overlaps)
    index = {p: i for i, p in enumerate(pairs)}
    for c in cp.creases:
        if c.facets not in index:
            index[c.facets] = len(pairs)
            pairs.append(c.facets)
    eqs = []
    for r in fo.rows:
        ps, const = r.equation()
        eqs.append(([index[p] for p in ps], const, r))
    labels = []
    if use_labels:
        for c in cp.creases:
            if c.assignment in ("M", "V"):
                a, b = c.facets
                s = 0 if c.assignment == "M" else 1
                labels.append((index[(a, b)], s ^ int(cp.side[a] < 0), c))
    return pairs, index, eqs, labels


def system_dict(cp: CreasePattern, use_labels: bool = True,
                triples_cap: int = 2_000_000) -> Dict:
    """The constraint system as a JSON-serialisable dictionary."""
    pairs, index, eqs, labels = _system(cp, use_labels)
    triples, complete = cp.folding.triples(triples_cap)
    return {
        "format": "linfold-system", "version": 1,
        "pattern": cp.name,
        "facets": cp.n_facets,
        "variables": [{"id": i, "facets": list(p),
                       "meaning": f"x[{p[0]},{p[1]}] = 1 iff facet {p[0]} lies below facet {p[1]}"}
                      for i, p in enumerate(pairs)],
        "creases": [{"id": c.id, "facets": list(c.facets), "label": c.assignment,
                     "variable": index[c.facets], "side_of_first_facet": cp.side[c.facets[0]]}
                    for c in cp.creases],
        "rows": [{"kind": r.kind, "creases": list(r.creases), "tortilla": r.tortilla,
                  "variables": cols, "rhs": const} for cols, const, r in eqs],
        "labels": [{"crease": c.id, "variable": v, "value": val} for v, val, c in labels],
        "transitivity": {"triples": [list(t) for t in triples], "complete": complete},
    }


def write_xnf(cp: CreasePattern, out: TextIO, use_labels: bool = True,
              triples_cap: int = 2_000_000) -> Dict[str, int]:
    """Write the system as DIMACS CNF with XOR clauses; returns counts."""
    pairs, index, eqs, labels = _system(cp, use_labels)
    triples, complete = cp.folding.triples(triples_cap)
    if not complete:
        raise ValueError(f"more than {triples_cap} transitivity triples; raise the cap")
    lines: List[str] = []
    nx = 0
    for cols, const, r in eqs:
        if not cols:
            if const:
                lines.append("0")                 # empty clause: unsatisfiable
            continue
        lits = [c + 1 for c in cols]
        if const == 0:                            # XOR of literals must be true
            lits[0] = -lits[0]
        lines.append("x" + " ".join(str(l) for l in lits) + " 0")
        nx += 1
    for v, val, _ in labels:
        lines.append(f"{v + 1 if val else -(v + 1)} 0")
    nt = 0
    for a, b, c in triples:
        x_ab, x_bc, x_ac = index[(a, b)] + 1, index[(b, c)] + 1, index[(a, c)] + 1
        # forbid the two cyclic orders: (x_ab, x_bc, x_ac) = (0, 0, 1), (1, 1, 0)
        lines.append(f"{x_ab} {x_bc} {-x_ac} 0")
        lines.append(f"{-x_ab} {-x_bc} {x_ac} 0")
        nt += 2
    out.write(f"c linfold: flat-folded states of {cp.name}\n")
    out.write(f"c variable v = x[a,b] for the v-th overlapping pair a < b "
              f"(true: facet a below facet b)\n")
    for i, (a, b) in enumerate(pairs):
        out.write(f"c {i + 1} = x[{a},{b}]\n")
    out.write(f"p cnf {len(pairs)} {len(lines)}\n")
    out.write("\n".join(lines) + ("\n" if lines else ""))
    return {"variables": len(pairs), "xor_clauses": nx, "unit_clauses": len(labels),
            "transitivity_clauses": nt}
