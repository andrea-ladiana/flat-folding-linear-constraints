"""The analysis of a crease pattern: local relations, global system, verdict.

:func:`analyze` runs three stages, from the cheapest to the strongest.

1. **Vertices.**  At every interior vertex the walk gives the rows
   (Lemma 1), the relations they impose on the assignment (Lemma 3; the pairs
   of Theorem 2 at vertices without taco--taco rows, the blocks of Theorem 4
   in general), the dimension of ``W_lin(v)`` and Hull's count of
   flat-foldable assignments.  A given mountain--valley labelling is tested
   against Maekawa's rule, the relations and Hull's recursion.

2. **Local system.**  The relations of all vertices, as a linear system on
   one bit per crease.  It is solved by elimination; if it is inconsistent,
   the pattern cannot fold flat, and the relations involved, expanded into
   their rows, form a certificate (the triangle pattern of Sec. 8 is the
   standard example).  Two convex facets meet in at most one vertex unless
   they share a crease, so the overlapping pairs of different vertices are
   distinct: this system is exactly the projection on the creases of all the
   rows at all the vertices.

3. **Global system.**  All taco--tortilla and taco--taco rows of the folded
   pattern, on the layer variables of all overlapping pairs, computed from the
   folded polygons.  It contains the local rows and more; its rank, its
   consistency and the dimension of its projection on the creases are
   reported, and Corollary 4 (the vertex rows add nothing) is checked.

The linear constraints are necessary conditions: inconsistency proves that no
flat-folded state exists, while consistency leaves the transitivity
constraints, where the NP-hardness of flat foldability lies, to be decided.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from .certificate import Certificate, Group, Item
from .f2 import AffineSystem
from .pattern import CreasePattern, Issue
from .rows import Row, canonical

__all__ = ["analyze", "Report", "VertexReport", "RelationInfo", "LevelReport"]


@dataclass
class RelationInfo:
    """A relation imposed by the rows at one vertex."""

    vertex: int
    creases: Tuple[int, ...]           #: crease ids
    parity: int                        #: number of valleys modulo 2
    rows: List[Row]                    #: the rows of its component
    kind: str                          #: 'equal', 'opposite' or 'block'
    extreme: bool = False              #: the pair of the extreme creases
    big_little_big: bool = False       #: the pair of a sector smaller than both neighbours

    def holds(self, labels: Dict[int, str]) -> Optional[bool]:
        if any(labels.get(c) not in ("M", "V") for c in self.creases):
            return None
        return sum(labels[c] == "V" for c in self.creases) % 2 == self.parity


@dataclass
class VertexReport:
    id: int
    point: Tuple[float, float]         #: file coordinates
    degree: int
    creases: List[int]
    facets: List[int]
    angles_deg: List[float]
    problem: Optional[str] = None
    generic: Optional[bool] = None
    tt: int = 0
    tc: int = 0
    gamma: int = 0
    E: int = 0
    dim_wlin: int = 0
    wlin: int = 0
    wflat: int = 0
    linear_equals_flat: Optional[bool] = None
    relations: List[RelationInfo] = field(default_factory=list)
    word: Optional[str] = None         #: the labels of its creases, if complete
    mv: Optional[int] = None
    maekawa: Optional[bool] = None
    in_wlin: Optional[bool] = None
    flat_foldable: Optional[bool] = None
    hull_failure: Optional[str] = None


@dataclass
class LevelReport:
    level: str                                      #: 'local' or 'global'
    variables: int = 0
    rows: Dict[str, int] = field(default_factory=dict)
    rank: int = 0
    consistent: bool = True
    certificate: Optional[Certificate] = None
    mv_dim: Optional[int] = None                    #: dim of the allowed assignments
    layer_dim: Optional[int] = None                 #: log2 of the solutions (global)
    labels_consistent: Optional[bool] = None
    labels_certificate: Optional[Certificate] = None
    forced: Dict[int, str] = field(default_factory=dict)   #: unlabelled creases forced
    vertex_rows_redundant: Optional[bool] = None    #: Corollary 4 (global)
    skipped: Optional[str] = None


@dataclass
class Report:
    name: str
    facets: int
    creases: int
    labels: Dict[str, int]
    interior_vertices: int
    issues: List[Issue]
    notes: List[str]
    vertices: List[VertexReport]
    relations: List[RelationInfo]
    local: LevelReport
    global_: Optional[LevelReport]
    verdict: str                       #: 'passes', 'not-flat-foldable', 'labels-not-flat-foldable'
    reason: str
    warnings: List[str] = field(default_factory=list)
    cp: Optional[CreasePattern] = field(default=None, repr=False)

    @property
    def certificate(self) -> Optional[Certificate]:
        """The certificate behind the verdict, if there is one."""
        for lvl in (self.local, self.global_):
            if lvl is None:
                continue
            if lvl.certificate is not None:
                return lvl.certificate
        for lvl in (self.local, self.global_):
            if lvl is not None and lvl.labels_certificate is not None:
                return lvl.labels_certificate
        return None

    @property
    def exit_code(self) -> int:
        return 0 if self.verdict == "passes" else 2


class InternalError(RuntimeError):
    pass


# ------------------------------------------------------------------ analyze
def analyze(cp: CreasePattern, *, global_system: bool = True,
            use_labels: bool = True, minimise: bool = True) -> Report:
    """Analyse a crease pattern; see the module docstring."""
    labels = {c.id: c.assignment for c in cp.creases if c.assignment in ("M", "V")} \
        if use_labels else {}
    counts = {"M": 0, "V": 0, "U": 0}
    for c in cp.creases:
        counts[c.assignment] = counts.get(c.assignment, 0) + 1

    vreports, relations = _vertices(cp, labels)
    local = _local(cp, relations, labels, minimise)
    glob = None
    warnings: List[str] = []
    if global_system:
        glob = _global(cp, labels, minimise, warnings)

    verdict, reason = _verdict(cp, vreports, local, glob, labels)
    return Report(cp.name, cp.n_facets, len(cp.creases), counts, len(cp.vertices),
                  list(cp.issues), list(cp.graph.notes), vreports, relations,
                  local, glob, verdict, reason, warnings, cp)


def _vertices(cp: CreasePattern, labels):
    import math
    out, relations = [], []
    for pv in cp.vertices:
        vr = VertexReport(pv.id, cp.original(pv.point), len(pv.creases),
                          list(pv.creases), list(pv.sectors),
                          [round(math.degrees(a), 9) for a in pv.angles], pv.problem)
        out.append(vr)
        v = pv.vertex
        if v is None:
            continue
        rows = cp.local_rows(pv)
        vr.generic, vr.tt, vr.tc = v.generic, len(v.tt_rows), len(v.tc_rows)
        vr.gamma, vr.E, vr.dim_wlin = v.gamma, v.E, v.dim_wlin
        vr.wlin, vr.wflat = v.wlin_count, v.wflat_count
        vr.linear_equals_flat = v.hull.linear_equals_flat
        blb = {frozenset((k0, k1)) for _, k0, k1, _ in v.big_little_big()}
        extreme = None if v.has_tc else frozenset((v.top[0], v.bottom[0]))
        for comp in v.components:
            rel = comp.relation
            if rel is None:
                continue
            local_set = frozenset(rel.creases)
            kind = ("block" if not rel.is_pair else
                    ("equal" if rel.equal else "opposite"))
            info = RelationInfo(pv.id, tuple(sorted(pv.creases[k] for k in rel.creases)),
                                rel.parity, [rows[i] for i in comp.rows], kind,
                                extreme == local_set, local_set in blb)
            vr.relations.append(info)
            relations.append(info)
        if all(c in labels for c in pv.creases):
            word = "".join(labels[c] for c in pv.creases)
            chk = v.check(word)
            vr.word, vr.mv, vr.maekawa = word, chk.mv, chk.maekawa
            vr.in_wlin, vr.flat_foldable = chk.in_wlin, chk.flat_foldable
            if chk.hull_failure:
                f = chk.hull_failure
                if f["crimp"] is None:
                    vr.hull_failure = (f"the last block has M - V = {f['sum']}, "
                                       f"not {f['need']}")
                else:
                    names = ", ".join(v.cname(k) for k in f["crimp"].creases)
                    vr.hull_failure = (f"crimping the sectors of angle "
                                       f"{math.degrees(f['crimp'].angle):.6g} deg, the "
                                       f"creases {names} have M - V = {f['sum']}, "
                                       f"not {f['need']}")
    return out, relations


def _label_item(cp: CreasePattern, c: int, label: str) -> Item:
    a, b = cp.creases[c].facets
    return Item("assignment", crease=c, label=label, facets=(a, b), side=cp.side[a])


def _local(cp, relations: List[RelationInfo], labels, minimise) -> LevelReport:
    rep = LevelReport("local")
    n = len(cp.creases)
    sysm = AffineSystem(n)
    for i, r in enumerate(relations):
        sysm.add(r.creases, r.parity, tag=("rel", i))
    rep.variables = n
    rep.rows = {"relations": len(relations),
                "rows": sum(len(r.rows) for r in relations)}
    sol = sysm.solve()
    rep.rank, rep.consistent = sol.rank, sol.consistent
    if not sol.consistent:
        rep.certificate = _local_certificate(cp, sysm, sol.certificate(minimise),
                                             relations, "pattern")
        return rep
    rep.mv_dim = n - sol.rank
    if not labels:
        return rep
    for c, lab in sorted(labels.items()):
        sysm.add([c], 0 if lab == "M" else 1, tag=("label", c))
    sol2 = sysm.solve()
    rep.labels_consistent = sol2.consistent
    if not sol2.consistent:
        rep.labels_certificate = _local_certificate(
            cp, sysm, sol2.certificate(minimise), relations, "assignment")
        return rep
    for c in range(n):
        if c not in labels and sol2.form(c).forced:
            rep.forced[c] = "M" if sol2.form(c).const == 0 else "V"
    return rep


def _local_certificate(cp, sysm, idx, relations, claim) -> Certificate:
    items: List[Item] = []
    groups: List[Group] = []
    for i in idx:
        tag = sysm.tags[i]
        if tag[0] == "rel":
            r = relations[tag[1]]
            start = len(items)
            items.extend(Item(row.kind, row=row) for row in r.rows)
            groups.append(Group(r.vertex, r.creases, r.parity,
                                list(range(start, len(items)))))
        else:
            c = tag[1]
            items.append(_label_item(cp, c, cp.creases[c].assignment))
    cert = Certificate(claim, "local", items, groups)
    if not cert.holds():
        raise InternalError("a local certificate does not add up to 0 = 1")
    return cert


def _global(cp: CreasePattern, labels, minimise, warnings) -> LevelReport:
    rep = LevelReport("global")
    if not cp.bipartite:
        rep.skipped = "the facets are not two-colourable"
        return rep
    if cp.nonconvex_facets:
        rep.skipped = (f"{len(cp.nonconvex_facets)} facet(s) are not convex; the "
                       "constraints of the paper assume convex facets")
        return rep
    fo = cp.folding
    if not fo.ok:
        rep.skipped = fo.message
        return rep
    sysm = AffineSystem()
    for p in fo.overlaps:
        sysm.var(p)
    for c in cp.creases:
        if not sysm.has_var(c.facets):
            warnings.append(f"the two facets of crease {c.id} do not overlap once "
                            "folded; the pattern is probably degenerate")
            sysm.var(c.facets)
    # rows that lie at a vertex first: elimination meets a contradiction among
    # them first when there is one, which keeps certificates local and short
    at_vertex = set()
    for pv in cp.vertices:
        if pv.vertex is not None:
            at_vertex.update((r.kind, tuple(sorted(r.creases)), r.tortilla)
                             for r in cp.local_rows(pv))
    rows = sorted(fo.rows, key=lambda r: (r.kind, tuple(sorted(r.creases)),
                                          r.tortilla) not in at_vertex)
    for i, r in enumerate(rows):
        pairs, const = r.equation()
        sysm.add([sysm.var(p) for p in pairs], const, tag=("row", i))
    rep.variables = sysm.n_vars
    rep.rows = {"TT": sum(r.kind == "TT" for r in rows),
                "TC": sum(r.kind == "TC" for r in rows)}
    sol = sysm.solve()
    rep.rank, rep.consistent = sol.rank, sol.consistent

    # the rows at every vertex, computed from the angles, are rows of the
    # folded polygons: a mismatch means a tolerance problem in the input
    keys = {(r.kind, tuple(sorted(r.creases)), r.tortilla, canonical(r.terms))
            for r in rows}
    bad = 0
    for pv in cp.vertices:
        if pv.vertex is None:
            continue
        for r in cp.local_rows(pv):
            if (r.kind, tuple(sorted(r.creases)), r.tortilla, canonical(r.terms)) not in keys:
                bad += 1
    if bad:
        warnings.append(f"{bad} row(s) found at the vertices from the angles are "
                        "missing from the folded polygons; the coordinates may be "
                        "too imprecise for the tolerances")

    # Corollary 4: the vertex rows change neither the rank nor the solutions
    ext = sysm.subsystem(range(len(sysm)))
    for pv in cp.vertices:
        if pv.vertex is None:
            continue
        d = len(pv.sectors)
        pairs, const = canonical([(pv.sectors[k], pv.sectors[(k + 1) % d])
                                  for k in range(d)])
        ext.add([ext.var(p) for p in pairs], const ^ 1, tag=("vertex", pv.id))
    sol_ext = ext.solve()
    rep.vertex_rows_redundant = (sol_ext.rank == sol.rank and
                                 sol_ext.consistent == sol.consistent)

    if not sol.consistent:
        idx = sol.certificate(minimise)
        rep.certificate = Certificate("pattern", "global",
                                      [Item(rows[sysm.tags[i][1]].kind,
                                            row=rows[sysm.tags[i][1]]) for i in idx])
        if not rep.certificate.holds():
            raise InternalError("a global certificate does not add up to 0 = 1")
        return rep
    rep.layer_dim = sol.nullity
    cols = [sysm.column(c.facets) for c in cp.creases]
    rep.mv_dim = sol.projection_rank(cols)
    if not labels:
        return rep
    for c, lab in sorted(labels.items()):
        a, b = cp.creases[c].facets
        s = 0 if lab == "M" else 1
        sysm.add([sysm.column((a, b))], s ^ int(cp.side[a] < 0), tag=("label", c))
    sol2 = sysm.solve()
    rep.labels_consistent = sol2.consistent
    if not sol2.consistent:
        items = []
        for i in sol2.certificate(minimise):
            tag = sysm.tags[i]
            if tag[0] == "row":
                items.append(Item(rows[tag[1]].kind, row=rows[tag[1]]))
            else:
                items.append(_label_item(cp, tag[1], labels[tag[1]]))
        rep.labels_certificate = Certificate("assignment", "global", items)
        if not rep.labels_certificate.holds():
            raise InternalError("a global certificate does not add up to 0 = 1")
        return rep
    for c in cp.creases:
        if c.id in labels:
            continue
        f = sol2.form(sysm.column(c.facets))
        if f.forced:
            s = f.const ^ int(cp.side[c.facets[0]] < 0)
            rep.forced[c.id] = "M" if s == 0 else "V"
    return rep


def _verdict(cp, vreports, local, glob, labels):
    fatal = cp.fatal_issues
    if fatal:
        kinds = sorted({i.kind for i in fatal})
        return "not-flat-foldable", ("the pattern violates a necessary condition: "
                                     + ", ".join(kinds))
    if not local.consistent:
        return "not-flat-foldable", ("the relations at the vertices are inconsistent "
                                     "(local linear certificate)")
    if glob is not None and glob.skipped is None and not glob.consistent:
        return "not-flat-foldable", ("the taco-tortilla and taco-taco rows are "
                                     "inconsistent (global linear certificate)")
    if labels:
        if local.labels_consistent is False:
            return "labels-not-flat-foldable", (
                "the mountain-valley labels violate the relations at the vertices "
                "(local linear certificate)")
        bad = [v for v in vreports if v.flat_foldable is False]
        if bad:
            return "labels-not-flat-foldable", (
                f"the labels are not flat-foldable at {len(bad)} vertex/vertices "
                "(Hull's crimping recursion)")
        if glob is not None and glob.labels_consistent is False:
            return "labels-not-flat-foldable", (
                "the labels are inconsistent with the taco-tortilla and taco-taco "
                "rows (global linear certificate)")
    return "passes", ("no obstruction found: the linear constraints are consistent; "
                      "whether a flat-folded state exists now depends on "
                      "transitivity (NP-hard in general)")
