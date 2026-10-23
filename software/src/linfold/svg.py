"""SVG drawings: a crease pattern with its certificate, and a single vertex.

The drawings are plain SVG 1.1 with no external resources.  Colours follow
the conventions of origami software (mountain red, valley blue) and the
figures of the paper (pairs in teal, amber and rose).
"""

from __future__ import annotations

import math
from typing import Dict, List, Optional, Sequence, Set, Tuple
from xml.sax.saxutils import escape

__all__ = ["pattern_svg", "vertex_svg"]

INK = "#1f2430"
MOUNTAIN = "#c8312f"
VALLEY = "#2457a6"
UNASSIGNED = "#8a8f99"
HIGHLIGHT = "#f2a516"
SIDE = ("#f4f1ea", "#e6e2f3")          # the two sides of the paper
PAIRS = ("#1b9e8a", "#d9822b", "#c2477a", "#5b6abf", "#7a9a2e", "#9b5fb0",
         "#2f8fbf", "#b8862b")


def _header(w: float, h: float, title: str) -> List[str]:
    return [f'<svg xmlns="http://www.w3.org/2000/svg" width="{w:.0f}" height="{h:.0f}" '
            f'viewBox="0 0 {w:.2f} {h:.2f}" font-family="Helvetica, Arial, sans-serif">',
            f"<title>{escape(title)}</title>",
            f'<rect width="{w:.2f}" height="{h:.2f}" fill="white"/>']


def pattern_svg(rep, size: float = 720.0) -> str:
    """The crease pattern of a :class:`linfold.analysis.Report`.

    Facets are tinted by the side of the paper they show once folded;
    creases are drawn with their labels (dashed for valleys, dotted for
    unassigned creases), labels forced by the linear constraints appear as
    thin coloured lines, and the creases, vertices and facets of the
    certificate, if there is one, are highlighted.
    """
    cp = rep.cp
    g = cp.graph
    xs = [p[0] for p in g.vertices]
    ys = [p[1] for p in g.vertices]
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    pad = 36.0
    k = (size - 2 * pad) / max(x1 - x0, y1 - y0, 1e-12)
    W = (x1 - x0) * k + 2 * pad
    legend_h = 64.0
    H = (y1 - y0) * k + 2 * pad + legend_h

    def P(p):
        return (pad + (p[0] - x0) * k, pad + (y1 - p[1]) * k)

    out = _header(W, H, f"linfold: {rep.name}")
    cert = rep.certificate
    hl_creases: Set[int] = set()
    hl_vertices: Set[int] = set()
    hl_facets: Set[int] = set()
    if cert is not None:
        for it in cert.items:
            if it.row is not None:
                hl_creases.update(it.row.creases)
                if it.row.vertex is not None:
                    hl_vertices.add(it.row.vertex)
                if it.row.tortilla is not None:
                    hl_facets.add(it.row.tortilla)
            else:
                hl_creases.add(it.crease)
        for gr in cert.groups:
            hl_vertices.add(gr.vertex)
    # facets
    for f, poly in enumerate(cp.facet_polygons):
        if len(poly) < 3:
            continue
        pts = " ".join(f"{P(p)[0]:.2f},{P(p)[1]:.2f}" for p in poly)
        fill = SIDE[0] if cp.side[f] >= 0 else SIDE[1]
        out.append(f'<polygon points="{pts}" fill="{fill}" stroke="none"/>')
        if f in hl_facets:
            out.append(f'<polygon points="{pts}" fill="{HIGHLIGHT}" fill-opacity="0.18" '
                       'stroke="none"/>')
    # highlight halo under the creases of the certificate
    for cid in sorted(hl_creases):
        for e in cp.creases[cid].edges:
            u, v = g.edges[e]
            (ax, ay), (bx, by) = P(g.vertices[u]), P(g.vertices[v])
            out.append(f'<line x1="{ax:.2f}" y1="{ay:.2f}" x2="{bx:.2f}" y2="{by:.2f}" '
                       f'stroke="{HIGHLIGHT}" stroke-width="9" stroke-linecap="round" '
                       'stroke-opacity="0.75"/>')
    forced: Dict[int, str] = {}
    for lvl in (rep.local, rep.global_):
        if lvl is not None and lvl.skipped is None:
            forced.update(lvl.forced)
    # edges
    for e, ((u, v), a) in enumerate(zip(g.edges, g.assignments)):
        (ax, ay), (bx, by) = P(g.vertices[u]), P(g.vertices[v])
        cid = cp.crease_of_edge.get(e)
        if a == "B" or (cid is None and a not in "F"):
            style = f'stroke="{INK}" stroke-width="2.2"'
        elif cid is None:
            style = f'stroke="{UNASSIGNED}" stroke-width="0.8" stroke-dasharray="2,3"'
        else:
            lab = cp.creases[cid].assignment
            if lab == "M":
                style = f'stroke="{MOUNTAIN}" stroke-width="2"'
            elif lab == "V":
                style = f'stroke="{VALLEY}" stroke-width="2" stroke-dasharray="7,4"'
            elif cid in forced:
                col = MOUNTAIN if forced[cid] == "M" else VALLEY
                dash = "" if forced[cid] == "M" else ' stroke-dasharray="7,4"'
                style = f'stroke="{col}" stroke-width="1.1" stroke-opacity="0.8"{dash}'
            else:
                style = f'stroke="{UNASSIGNED}" stroke-width="1.4" stroke-dasharray="1.5,3"'
        out.append(f'<line x1="{ax:.2f}" y1="{ay:.2f}" x2="{bx:.2f}" y2="{by:.2f}" '
                   f'{style} stroke-linecap="round"/>')
    # vertices
    for vr in rep.vertices:
        x, y = P(cp.vertices[vr.id].point)
        bad = vr.problem or vr.flat_foldable is False or vr.in_wlin is False
        if vr.id in hl_vertices:
            out.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="9" fill="none" '
                       f'stroke="{HIGHLIGHT}" stroke-width="3"/>')
        if bad:
            out.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="6" fill="none" '
                       f'stroke="{MOUNTAIN}" stroke-width="2"/>')
        out.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="2.2" fill="{INK}"/>')
    # legend
    ly = H - legend_h + 18
    verdict = {"passes": "passes the linear filters",
               "not-flat-foldable": "not flat-foldable",
               "labels-not-flat-foldable": "not flat-foldable with these labels"}[rep.verdict]
    out.append(f'<text x="{pad:.1f}" y="{ly:.1f}" font-size="15" fill="{INK}" '
               f'font-weight="bold">{escape(rep.name)}: {escape(verdict)}</text>')
    items = [("mountain", MOUNTAIN, ""), ("valley", VALLEY, "7,4"),
             ("unassigned", UNASSIGNED, "1.5,3")]
    if forced:
        items.append(("forced by the rows", MOUNTAIN, ""))
    if cert is not None:
        items.append((f"certificate ({len(cert.items)} equations)", HIGHLIGHT, ""))
    lx = pad
    for name, col, dash in items:
        d = f' stroke-dasharray="{dash}"' if dash else ""
        wdt = 7 if name.startswith("certificate") else 2
        out.append(f'<line x1="{lx:.1f}" y1="{ly + 22:.1f}" x2="{lx + 26:.1f}" '
                   f'y2="{ly + 22:.1f}" stroke="{col}" stroke-width="{wdt}"{d}/>')
        out.append(f'<text x="{lx + 32:.1f}" y="{ly + 26:.1f}" font-size="12" '
                   f'fill="{INK}">{escape(name)}</text>')
        lx += 44 + 6.6 * len(name)
    out.append("</svg>")
    return "\n".join(out) + "\n"


def vertex_svg(v, word: Optional[str] = None, width: float = 760.0) -> str:
    """The walk of a vertex as a height function, with its pairs or blocks.

    Creases are placed left to right in their cyclic order starting after
    the lowest crease, at the height ``c_k`` of their ray; the sectors are
    the segments between them.  Below, every relation is drawn as arcs
    joining its creases (Theorem 2, Fig. 3c of the paper); taco--taco rows
    are marked by squares.
    """
    n = v.n
    B = v.bottom[0]
    order = [(B + 1 + i) % n for i in range(n)]       # creases after e_B, ending with e_B
    seq = [B] + order                                  # the walk starts and ends at e_B
    pos = [float(v.pos[k]) for k in range(n)]
    lo, hi = min(pos), max(pos)
    pad, top_h = 48.0, 230.0
    dx = (width - 2 * pad) / n
    X = {i: pad + i * dx for i in range(n + 1)}
    where = {k: i for i, k in enumerate(seq[:-1])}
    axis_y = top_h - 10
    base = axis_y + 26
    # arcs of the relations: a cubic from end to end reaches 3/4 of its depth
    arcs = []
    for j, rel in enumerate(v.relations):
        xs = sorted(X[where[k]] for k in rel.creases)
        segs = [(a, b, 10 + (b - a) * 0.22) for a, b in zip(xs, xs[1:])]
        arcs.append((j, rel, segs))
    bottom = max((base + 0.75 * d for _, _, segs in arcs for _, _, d in segs), default=base)
    H = bottom + 24 + 44

    def Y(c):
        return 30 + (hi - c) / (hi - lo or 1) * (top_h - 60)

    out = _header(width, H, "linfold: vertex walk")
    # sectors
    pts = " ".join(f"{X[i]:.2f},{Y(pos[k]):.2f}" for i, k in enumerate(seq))
    out.append(f'<polyline points="{pts}" fill="none" stroke="{INK}" stroke-width="1.6"/>')
    sigma = None
    if word is not None:
        from .vertex import parse_assignment
        sigma = parse_assignment(word, n)
    # creases
    for i, k in enumerate(seq):
        x, y = X[i], Y(pos[k])
        out.append(f'<line x1="{x:.2f}" y1="{y:.2f}" x2="{x:.2f}" y2="{axis_y:.2f}" '
                   f'stroke="{UNASSIGNED}" stroke-width="0.6" stroke-dasharray="2,3"/>')
        col = INK if sigma is None else (MOUNTAIN if sigma[k] > 0 else VALLEY)
        out.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="4" fill="{col}"/>')
        if i < n:
            out.append(f'<text x="{x:.2f}" y="{axis_y + 16:.2f}" font-size="12" '
                       f'text-anchor="middle" fill="{INK}">{escape(v.cname(k))}</text>')
    tc_creases = {k for r in v.tc_rows for k in r.creases}
    for i, k in enumerate(seq[:-1]):
        if k in tc_creases:
            x, y = X[i], Y(pos[k])
            out.append(f'<rect x="{x - 6:.2f}" y="{y - 6:.2f}" width="12" height="12" '
                       f'fill="none" stroke="{HIGHLIGHT}" stroke-width="2"/>')
    # relations as arcs below the axis, each labelled under its lowest point
    for j, rel, segs in arcs:
        col = PAIRS[j % len(PAIRS)]
        for a, b, d in segs:
            out.append(f'<path d="M {a:.2f} {base:.2f} C {a:.2f} {base + d:.2f} '
                       f'{b:.2f} {base + d:.2f} {b:.2f} {base:.2f}" fill="none" '
                       f'stroke="{col}" stroke-width="2.2"/>')
        a, b, d = max(segs, key=lambda t: t[2])
        label = ("equal" if rel.equal else "opposite") if rel.is_pair else (
            "even V" if rel.parity == 0 else "odd V")
        out.append(f'<text x="{(a + b) / 2:.2f}" y="{base + 0.75 * d + 12:.2f}" '
                   f'font-size="10" text-anchor="middle" fill="{col}">{label}</text>')
    title = (f"degree {n}: {len(v.tt_rows)} taco-tortilla, {len(v.tc_rows)} taco-taco rows; "
             f"|W_lin| = {v.wlin_count}, |W_flat| = {v.wflat_count}")
    out.append(f'<text x="{pad:.1f}" y="{H - 18:.1f}" font-size="13" fill="{INK}">'
               f"{escape(title)}</text>")
    out.append("</svg>")
    return "\n".join(out) + "\n"
