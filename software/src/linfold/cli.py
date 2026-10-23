"""Command-line interface: ``linfold vertex | check | verify | export``.

Exit status: 0 when no obstruction is found, 2 when the pattern (or the
labelled pattern, or the vertex assignment) is proved not flat-foldable, 1 on
an error in the input.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from typing import List, Optional

from . import __version__

EPILOG = """\
examples:
  linfold vertex 40 70 100 60 40 50
  linfold vertex 45 135 135 45 --mv VMVV
  linfold check pattern.fold
  linfold check pattern.cp --certificate cert.json --svg pattern.svg
  linfold verify cert.json --pattern pattern.cp
  linfold export pattern.fold --format xnf -o pattern.cnf

The paper: A. Ladiana, "Maekawa's theorem and the linear constraints of flat
folding".  https://github.com/andrea-ladiana/flat-folding-linear-constraints
"""


def _angle(text: str):
    """Parse an angle exactly when possible ('40', '22.5', '135/2')."""
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError):
        raise argparse.ArgumentTypeError(f"not a number: {text!r}")


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="linfold",
        description="The linear constraints of flat folding: rows, pairs, blocks "
                    "and certificates of non-flat-foldability for origami crease "
                    "patterns.",
        epilog=EPILOG, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--version", action="version", version=f"linfold {__version__}")
    sub = p.add_subparsers(dest="command", metavar="COMMAND")

    v = sub.add_parser("vertex", help="analyse a single vertex given its sector angles",
                       description="Analyse a single vertex (or a closed walk) from its "
                                   "sector angles in degrees, in cyclic order. Angles "
                                   "are read exactly ('22.5' and '45/2' are the same).")
    v.add_argument("angles", nargs="+", type=_angle, metavar="ANGLE")
    v.add_argument("--mv", metavar="WORD", help="a mountain-valley word to test, e.g. MMMV")
    v.add_argument("--list", action="store_true",
                   help="list the assignments in W_lin and W_flat (small degree)")
    v.add_argument("--cone", action="store_true",
                   help="allow angles that do not add up to 360 (vertex of a cone)")
    v.add_argument("--json", action="store_true", help="print JSON")
    v.add_argument("--svg", metavar="FILE", help="draw the walk and its relations")

    c = sub.add_parser("check", help="analyse a crease pattern file",
                       description="Analyse a crease pattern (.fold, .cp, .opx, .svg): "
                                   "the relations at every vertex, the local and the "
                                   "global linear systems, and the labels of the file.")
    c.add_argument("pattern")
    c.add_argument("--local", action="store_true",
                   help="skip the global system (no folding of the polygons)")
    c.add_argument("--ignore-labels", action="store_true",
                   help="ignore the mountain-valley labels of the file")
    c.add_argument("--format", choices=["text", "markdown", "json"], default="text")
    c.add_argument("-v", "--verbose", action="store_true", help="show every vertex")
    c.add_argument("--certificate", metavar="FILE",
                   help="write the certificate (JSON), if one is found")
    c.add_argument("--svg", metavar="FILE", help="draw the pattern and the certificate")
    c.add_argument("--complete", metavar="FILE",
                   help="write a FOLD file with the labels forced by the rows filled in")
    c.add_argument("--angle-tol", type=float, default=None, metavar="RAD",
                   help="crease rays closer than this coincide (default 1e-6)")
    c.add_argument("--kawasaki-tol", type=float, default=None, metavar="RAD",
                   help="tolerance on Kawasaki's alternating sum (default 1e-4)")
    c.add_argument("--no-minimise", action="store_true",
                   help="do not reduce certificates to an inclusion-minimal set")

    r = sub.add_parser("verify", help="check a certificate",
                       description="Check that the equations of a certificate add up "
                                   "to 0 = 1 and, given the pattern, that each one is a "
                                   "constraint of it.")
    r.add_argument("certificate")
    r.add_argument("--pattern", metavar="FILE", help="the crease pattern to check against")

    e = sub.add_parser("export", help="export the constraint system",
                       description="Export the layer variables, the linear rows and the "
                                   "transitivity triples (JSON), or a CNF formula with XOR "
                                   "clauses (XNF, for CryptoMiniSat).")
    e.add_argument("pattern")
    e.add_argument("-o", "--output", required=True, metavar="FILE")
    e.add_argument("--format", choices=["json", "xnf"], default="json")
    e.add_argument("--ignore-labels", action="store_true")
    return p


# ------------------------------------------------------------------ commands
def cmd_vertex(a) -> int:
    from .report import dumps, vertex_json, vertex_text
    from .svg import vertex_svg
    from .vertex import Vertex, VertexError
    total = sum(a.angles)
    if not a.cone and total != 360:
        print(f"error: the angles add up to {float(total):g}, not 360 degrees "
              "(use --cone for the vertex of a cone)", file=sys.stderr)
        return 1
    try:
        v = Vertex(a.angles)
        if a.mv:
            v.check(a.mv)
    except (VertexError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    v.verify_theorems()
    if a.json:
        print(dumps(vertex_json(v, a.mv)))
    else:
        sys.stdout.write(vertex_text(v, a.mv, a.list))
    if a.svg:
        with open(a.svg, "w", encoding="utf-8") as fh:
            fh.write(vertex_svg(v, a.mv))
    if a.mv and not v.check(a.mv).flat_foldable:
        return 2
    return 0


def _load(path: str, a=None):
    from .pattern import load
    kw = {}
    if a is not None and getattr(a, "angle_tol", None) is not None:
        kw["angle_tol"] = a.angle_tol
    if a is not None and getattr(a, "kawasaki_tol", None) is not None:
        kw["kawasaki_tol"] = a.kawasaki_tol
    return load(path, **kw)


def cmd_check(a) -> int:
    from .analysis import analyze
    from .report import dumps, json_report, markdown_report, text_report
    from .svg import pattern_svg
    cp = _load(a.pattern, a)
    rep = analyze(cp, global_system=not a.local, use_labels=not a.ignore_labels,
                  minimise=not a.no_minimise)
    if a.format == "json":
        print(dumps(json_report(rep)))
    elif a.format == "markdown":
        sys.stdout.write(markdown_report(rep))
    else:
        sys.stdout.write(text_report(rep, verbose=a.verbose))
    if a.certificate:
        cert = rep.certificate
        if cert is None:
            print("no certificate: no linear obstruction was found", file=sys.stderr)
        else:
            with open(a.certificate, "w", encoding="utf-8") as fh:
                json.dump(cert.to_json(cp, source=a.pattern), fh, indent=1)
                fh.write("\n")
    if a.svg:
        with open(a.svg, "w", encoding="utf-8") as fh:
            fh.write(pattern_svg(rep))
    if a.complete:
        _write_completed(rep, a.complete)
    return rep.exit_code


def _write_completed(rep, path: str) -> None:
    from .formats import write_fold
    cp = rep.cp
    forced = dict(rep.local.forced)
    if rep.global_ is not None and rep.global_.skipped is None:
        forced.update(rep.global_.forced)
    g = cp.graph
    assign = list(g.assignments)
    for cid, lab in forced.items():
        for e in cp.creases[cid].edges:
            if assign[e] == "U":
                assign[e] = lab
    write_fold(path, [cp.original(p) for p in g.vertices], g.edges, assign,
               title=f"{rep.name} with forced labels")


def cmd_verify(a) -> int:
    from .certificate import load_certificate, verify
    doc = load_certificate(a.certificate)
    cp = _load(a.pattern) if a.pattern else None
    res = verify(doc, cp)
    for m in res.messages:
        print(m)
    if res.ok:
        print("VALID" + ("" if cp is not None else
                         " (algebra only; pass --pattern to check the geometry)"))
        return 0
    print("INVALID")
    return 2


def cmd_export(a) -> int:
    from .export import system_dict, write_xnf
    cp = _load(a.pattern)
    if a.format == "json":
        with open(a.output, "w", encoding="utf-8") as fh:
            json.dump(system_dict(cp, not a.ignore_labels), fh, indent=1)
            fh.write("\n")
    else:
        with open(a.output, "w", encoding="utf-8", newline="\n") as fh:
            counts = write_xnf(cp, fh, not a.ignore_labels)
        print(", ".join(f"{v} {k.replace('_', ' ')}" for k, v in counts.items()))
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    a = parser.parse_args(argv)
    if a.command is None:
        parser.print_help()
        return 1
    from .formats import FormatError
    from .planar import PlanarityError
    try:
        return {"vertex": cmd_vertex, "check": cmd_check, "verify": cmd_verify,
                "export": cmd_export}[a.command](a)
    except (FormatError, PlanarityError, ValueError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":       # pragma: no cover
    sys.exit(main())
