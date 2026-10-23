"""Human-readable and machine-readable renderings of the analyses."""

from __future__ import annotations

import json
import math
from typing import Dict, List, Optional

from . import __version__
from .analysis import Report
from .certificate import Certificate
from .vertex import Vertex

__all__ = ["text_report", "markdown_report", "json_report", "vertex_text", "vertex_json"]

RULE = "-" * 72


def _c(k: int) -> str:
    return f"c{k}"


def _f(i: int) -> str:
    return f"F{i}"


def _pt(p) -> str:
    x, y = (0.0 if abs(t) < 1e-10 else t for t in p)
    return f"({x:.6g}, {y:.6g})"


def _pow(d: Optional[int]) -> str:
    return "-" if d is None else f"2^{d}"


# ------------------------------------------------------------------ pattern
def _relation_text(r) -> str:
    names = ", ".join(_c(c) for c in r.creases)
    if r.kind == "block":
        mod4 = (len(r.creases) - 2 * r.parity) % 4
        return (f"{{{names}}} {'even' if r.parity == 0 else 'odd'} number of valleys "
                f"(M - V = {mod4} mod 4)")
    tag = " [extreme]" if r.extreme else (" [big-little-big]" if r.big_little_big else "")
    return f"{names} {r.kind}{tag}"


def _certificate_lines(cert: Certificate, cp) -> List[str]:
    out = []
    head = "pattern" if cert.claim == "pattern" else "labelled pattern"
    out.append(f"Certificate: {len(cert.items)} equations ({cert.level}) prove that "
               f"the {head} has no flat-folded state")
    grouped = set()
    for g in cert.groups:
        v = cp.vertices[g.vertex]
        names = ", ".join(_c(c) for c in g.creases)
        if len(g.creases) == 2:
            rel = "opposite" if g.parity == 1 else "equal"
            out.append(f"  at vertex v{g.vertex} {_pt(cp.original(v.point))}: "
                       f"{names} {rel}")
        else:
            out.append(f"  at vertex v{g.vertex} {_pt(cp.original(v.point))}: "
                       f"{{{names}}} {'even' if g.parity == 0 else 'odd'} "
                       "number of valleys")
        for i in g.items:
            out.append("      " + cert.items[i].row.describe(_c, _f))
            grouped.add(i)
    for i, it in enumerate(cert.items):
        if i in grouped:
            continue
        if it.kind == "assignment":
            a, b = it.facets
            s = 0 if it.label == "M" else 1
            rhs = s ^ int(it.side < 0)
            out.append(f"  label {_c(it.crease)} = {it.label}:  x[{_f(a)},{_f(b)}] = {rhs}")
        else:
            out.append("  " + it.row.describe(_c, _f))
    out.append("  sum of all left-hand sides: 0;  sum of the constants: 1")
    return out


def text_report(rep: Report, verbose: bool = False) -> str:
    cp = rep.cp
    L: List[str] = []
    L.append(f"linfold {__version__}  --  {rep.name}")
    L.append(RULE)
    lab = rep.labels
    L.append(f"Pattern   {rep.facets} facets, {rep.creases} creases "
             f"({lab.get('M', 0)} M, {lab.get('V', 0)} V, {lab.get('U', 0)} unassigned), "
             f"{rep.interior_vertices} interior vertices")
    verdict = {"passes": "PASSES the linear filters",
               "not-flat-foldable": "NOT FLAT-FOLDABLE",
               "labels-not-flat-foldable": "NOT FLAT-FOLDABLE with these labels"}
    L.append(f"Verdict   {verdict[rep.verdict]}")
    L.append(f"          {rep.reason}")
    for n in rep.notes:
        L.append(f"Note      {n}")
    for i in rep.issues:
        where = f" at {_pt(i.where)}" if i.where else ""
        L.append(f"{'Problem' if i.fatal else 'Warning'}   {i.message}{where}")
    for w in rep.warnings:
        L.append(f"Warning   {w}")

    L.append("")
    L.append("Vertices")
    shown = rep.vertices if verbose or len(rep.vertices) <= 12 else rep.vertices[:12]
    for v in shown:
        L.append(f"  v{v.id} {_pt(v.point)}  degree {v.degree}"
                 + (f"  -- {v.problem}" if v.problem else ""))
        if v.problem:
            continue
        kind = "generic" if v.generic else ("taco-taco rows" if v.tc else "degenerate")
        L.append(f"      {kind}; rows {v.tt} TT + {v.tc} TC; components gamma = {v.gamma}; "
                 f"|W_lin| = 2^{v.dim_wlin} = {v.wlin}, |W_flat| = {v.wflat}"
                 + ("" if v.linear_equals_flat else "  (W_lin is larger)"))
        L.append("      relations: " + "; ".join(_relation_text(r) for r in v.relations))
        if v.word is not None:
            verdicts = []
            verdicts.append(f"M-V = {v.mv:+d}")
            verdicts.append("relations ok" if v.in_wlin else "relations VIOLATED")
            verdicts.append("flat-foldable" if v.flat_foldable else "NOT flat-foldable")
            L.append(f"      labels {v.word}: " + ", ".join(verdicts))
            if v.hull_failure:
                L.append(f"      Hull's recursion: {v.hull_failure}")
    if len(shown) < len(rep.vertices):
        L.append(f"  ... {len(rep.vertices) - len(shown)} more (use --verbose)")

    L.append("")
    loc = rep.local
    L.append("Local system: the relations at the vertices, one bit per crease")
    L.append(f"  {loc.variables} creases, {loc.rows.get('relations', 0)} relations "
             f"(sums of {loc.rows.get('rows', 0)} rows), rank {loc.rank}: "
             + ("consistent" if loc.consistent else "INCONSISTENT"))
    if loc.consistent:
        L.append(f"  mountain-valley assignments allowed: {_pow(loc.mv_dim)} "
                 f"of 2^{loc.variables}")
        if loc.labels_consistent is not None:
            L.append("  with the labels of the file: "
                     + ("consistent" if loc.labels_consistent else "INCONSISTENT"))
        if loc.forced:
            L.append(f"  forced labels of unassigned creases: {len(loc.forced)}")
    g = rep.global_
    if g is not None:
        L.append("")
        L.append("Global system: all taco-tortilla and taco-taco rows of the folded pattern")
        if g.skipped:
            L.append(f"  skipped: {g.skipped}")
        else:
            L.append(f"  {g.variables} layer variables, {g.rows.get('TT', 0)} TT + "
                     f"{g.rows.get('TC', 0)} TC rows, rank {g.rank}: "
                     + ("consistent" if g.consistent else "INCONSISTENT"))
            if g.consistent:
                L.append(f"  layer orders allowed by the linear rows: {_pow(g.layer_dim)} "
                         f"of 2^{g.variables}; mountain-valley assignments: "
                         f"{_pow(g.mv_dim)}")
                if g.labels_consistent is not None:
                    L.append("  with the labels of the file: "
                             + ("consistent" if g.labels_consistent else "INCONSISTENT"))
                if g.forced:
                    L.append(f"  forced labels of unassigned creases: {len(g.forced)}")
            if g.vertex_rows_redundant is not None:
                L.append("  Corollary 4: the vertex rows change neither rank nor "
                         "solutions: " + ("yes" if g.vertex_rows_redundant else "NO"))
    cert = rep.certificate
    if cert is not None:
        L.append("")
        L.extend(_certificate_lines(cert, cp))
    forced = (g.forced if g is not None and g.skipped is None and g.forced else
              rep.local.forced)
    if forced and verbose:
        L.append("")
        L.append("Forced labels: " + ", ".join(f"{_c(c)}={a}" for c, a in sorted(forced.items())))
    return "\n".join(L) + "\n"


def markdown_report(rep: Report) -> str:
    body = text_report(rep, verbose=True)
    return f"# linfold report: {rep.name}\n\n```text\n{body}```\n"


def json_report(rep: Report) -> Dict:
    cp = rep.cp

    def rel(r):
        return {"vertex": r.vertex, "creases": list(r.creases), "kind": r.kind,
                "valley_parity": r.parity, "extreme": r.extreme,
                "big_little_big": r.big_little_big,
                "rows": [r_.describe(_c, _f) for r_ in r.rows]}

    def level(lv):
        if lv is None:
            return None
        return {"variables": lv.variables, "rows": lv.rows, "rank": lv.rank,
                "consistent": lv.consistent, "mv_dimension": lv.mv_dim,
                "layer_dimension": lv.layer_dim,
                "labels_consistent": lv.labels_consistent,
                "forced": {str(c): a for c, a in sorted(lv.forced.items())},
                "vertex_rows_redundant": lv.vertex_rows_redundant,
                "skipped": lv.skipped,
                "certificate": (lv.certificate or lv.labels_certificate).to_json(cp)
                if (lv.certificate or lv.labels_certificate) else None}

    return {
        "format": "linfold-report", "version": 1, "linfold": __version__,
        "pattern": {"name": rep.name, "facets": rep.facets, "creases": rep.creases,
                    "labels": rep.labels, "interior_vertices": rep.interior_vertices},
        "verdict": rep.verdict, "reason": rep.reason,
        "issues": [{"kind": i.kind, "message": i.message, "fatal": i.fatal,
                    "where": list(i.where) if i.where else None} for i in rep.issues],
        "notes": rep.notes, "warnings": rep.warnings,
        "creases": [{"id": c.id, "facets": list(c.facets), "label": c.assignment,
                     "segment": [list(cp.original(c.segment[0])),
                                 list(cp.original(c.segment[1]))]}
                    for c in cp.creases],
        "vertices": [{"id": v.id, "point": list(v.point), "degree": v.degree,
                      "creases": v.creases, "facets": v.facets,
                      "angles_deg": v.angles_deg, "problem": v.problem,
                      "generic": v.generic, "tt_rows": v.tt, "tc_rows": v.tc,
                      "gamma": v.gamma, "E": v.E, "dim_wlin": v.dim_wlin,
                      "wlin": v.wlin, "wflat": v.wflat,
                      "linear_equals_flat": v.linear_equals_flat,
                      "relations": [rel(r) for r in v.relations],
                      "labels": v.word, "mv": v.mv, "in_wlin": v.in_wlin,
                      "flat_foldable": v.flat_foldable,
                      "hull_failure": v.hull_failure} for v in rep.vertices],
        "local": level(rep.local),
        "global": level(rep.global_),
    }


# ------------------------------------------------------------------- vertex
def _word(sigma) -> str:
    return "".join("M" if s > 0 else "V" for s in sigma)


def vertex_text(v: Vertex, word: Optional[str] = None, list_words: bool = False,
                unit: str = "deg") -> str:
    L: List[str] = []
    n = v.n
    L.append(f"linfold {__version__}  --  vertex of degree {n}")
    L.append(RULE)
    ang = ", ".join(_num(a) for a in v.angles)
    L.append(f"Angles      {ang} {unit}   (sum {_num(sum(v.angles))})")
    L.append("Walk        c = (" + ", ".join(_num(p) for p in v.pos) + ")   "
             "[c_k is the ray of crease e_k; maxima: "
             + ", ".join(v.cname(k) for k in range(n) if v.is_max(k)) + "]")
    if v.generic:
        kind = "generic"
    elif v.has_tc:
        kind = "degenerate, with taco-taco rows"
    else:
        kind = "degenerate (a maximum and a minimum share a ray), no taco-taco row"
    L.append(f"Type        {kind}")
    L.append(f"Extremes    top {', '.join(v.cname(k) for k in v.top)}; "
             f"bottom {', '.join(v.cname(k) for k in v.bottom)}")
    L.append("")
    L.append(f"Rows (Lemma 1): {len(v.tt_rows)} taco-tortilla, {len(v.tc_rows)} taco-taco, "
             f"on {len(v.overlapping_pairs)} overlapping pairs of sectors; rank {v.rank()}")
    for r in v.rows:
        L.append("  " + v.describe_row(r))
    L.append("")
    L.append(f"Theorem 1   sum of all rows = vertex row (Maekawa mod 4): "
             f"{'yes' if v.theorem1_holds() else 'NO'}")
    L.append(f"Lemma 3     {v.gamma} component(s) with adjacent pairs: "
             f"dim W_lin = {n} - {v.gamma} = {v.dim_wlin}, |W_lin| = {v.wlin_count}")
    L.append("Relations   " + "\n            ".join(v.describe_relation(r) for r in v.relations))
    if v.pairs is not None:
        L.append("")
        L.append("Theorem 2   pairs of creases, joined by paths of the row graph:")
        for p in v.pairs:
            a, b = p.creases
            ex = "   [extreme creases]" if set(p.creases) == {v.top[0], v.bottom[0]} else ""
            path = " -> ".join(f"{v.cname(v.rows[i].creases[0])}|{v.fname(v.rows[i].tortilla)}"
                               for i in p.rows) or "(no row)"
            L.append(f"  {v.cname(a)}, {v.cname(b)}: {'equal' if p.equal else 'opposite'}"
                     f"{ex}\n      path {path}")
        L.append(f"  cycles of the row graph: {v.cycles}; rank N - m - c = "
                 f"{len(v.overlapping_pairs)} - {v.m} - {v.cycles} = "
                 f"{len(v.overlapping_pairs) - v.m - v.cycles} (Proposition 2)")
        pers = v.persistence_pairs()
        L.append("Theorem 3   persistence pairs (minimum, maximum): "
                 + ", ".join(f"({v.cname(a)}, {v.cname(b)})" for a, b in pers)
                 + "  -- the last is the essential pair")
        L.append(f"Prop. 1     pairs nested (no crossing chords): "
                 f"{'yes' if v.nested() else 'NO'}")
    blb = v.big_little_big()
    if blb:
        L.append("Prop. 4     big-little-big: " + "; ".join(
            f"{v.fname(i)} smaller than its neighbours -> {v.cname(a)}, {v.cname(b)} opposite"
            for i, a, b, _ in blb))
    L.append("")
    h = v.hull
    L.append(f"Hull's recursion (Sec. 7): {len(h.crimps)} crimp(s), E = {h.E} with k even")
    for c in h.crimps:
        names = ", ".join(v.cname(k) for k in c.creases)
        star = f" -> {v.cname(c.star)}" if c.star is not None else ""
        L.append(f"  angle {_num(c.angle)}: run of {c.k + 1} sector(s), creases {names}{star}"
                 f"  ({'M - V = 0' if c.even else 'M - V = +-1'})")
    L.append(f"  final walk: {', '.join(v.cname(k) for k in h.final)}  (M - V = +-2)")
    L.append(f"Theorem 4   W_lin = aff W_flat = W_4, dim {h.dim_w4}; blocks = components: "
             f"{'yes' if v.theorem4_holds() else 'NO'}")
    L.append(f"Corollary 2 |W_flat| = {v.wflat_count} (Hull), |W_lin| = {v.wlin_count}: "
             + ("the linear constraints decide flat-foldability here"
                if h.linear_equals_flat else "transitivity is needed here"))
    if word is not None:
        chk = v.check(word)
        L.append("")
        L.append(f"Assignment  {_word(chk.sigma)}:  M - V = {chk.mv:+d}")
        L.append(f"  Maekawa mod 4: {'yes' if chk.maekawa_mod4 else 'NO'};  "
                 f"Maekawa: {'yes' if chk.maekawa else 'NO'};  "
                 f"big-little-big: {'yes' if not chk.big_little_big else 'NO'}")
        L.append(f"  induced by a solution of the rows (in W_lin): "
                 f"{'yes' if chk.in_wlin else 'NO'}")
        for comp in chk.violated:
            L.append(f"    violated: {v.describe_relation(comp.relation)}, the sum of")
            for i in comp.rows:
                L.append("      " + v.describe_row(v.rows[i]))
        L.append(f"  flat-foldable (Hull): {'yes' if chk.flat_foldable else 'NO'}")
        if chk.hull_failure:
            f = chk.hull_failure
            if f["crimp"] is None:
                L.append(f"    the final block has M - V = {f['sum']}, not {f['need']}")
            else:
                names = ", ".join(v.cname(k) for k in f["crimp"].creases)
                L.append(f"    crimping the sectors of angle {_num(f['crimp'].angle)}: "
                         f"creases {names} have M - V = {f['sum']}, not {f['need']}")
    if list_words:
        L.append("")
        L.append("W_lin:  " + " ".join(_word(s) for s in v.wlin_words()))
        L.append("W_flat: " + " ".join(_word(s) for s in v.wflat_words()))
    return "\n".join(L) + "\n"


def _num(x) -> str:
    if isinstance(x, float):
        return f"{x:.10g}"
    return str(x)


def vertex_json(v: Vertex, word: Optional[str] = None) -> Dict:
    def num(x):
        return float(x) if not isinstance(x, int) else x
    d = {
        "format": "linfold-vertex", "version": 1, "linfold": __version__,
        "angles": [num(a) for a in v.angles], "walk": [num(p) for p in v.pos],
        "generic": v.generic, "taco_taco": v.has_tc,
        "rows": [{"kind": r.kind, "creases": [k + 1 for k in r.creases],
                  "tortilla": None if r.tortilla is None else r.tortilla + 1,
                  "text": v.describe_row(r)} for r in v.rows],
        "overlapping_pairs": len(v.overlapping_pairs), "rank": v.rank(),
        "theorem1": v.theorem1_holds(),
        "gamma": v.gamma, "dim_wlin": v.dim_wlin, "wlin": v.wlin_count,
        "relations": [{"creases": [k + 1 for k in r.creases], "valley_parity": r.parity,
                       "text": v.describe_relation(r)} for r in v.relations],
        "pairs": None if v.pairs is None else [
            {"creases": [k + 1 for k in p.creases], "equal": p.equal} for p in v.pairs],
        "persistence_pairs": None if v.has_tc else [
            [a + 1, b + 1] for a, b in v.persistence_pairs()],
        "E": v.E, "wflat": v.wflat_count,
        "linear_equals_flat": v.hull.linear_equals_flat,
        "blocks": [sorted(k + 1 for k in b.creases) for b in v.hull.blocks],
    }
    if word is not None:
        c = v.check(word)
        d["assignment"] = {"word": _word(c.sigma), "mv": c.mv, "maekawa": c.maekawa,
                           "in_wlin": c.in_wlin, "flat_foldable": c.flat_foldable,
                           "violated": [[k + 1 for k in comp.relation.creases]
                                        for comp in c.violated]}
    return d


def dumps(obj) -> str:
    return json.dumps(obj, indent=2, ensure_ascii=False)
