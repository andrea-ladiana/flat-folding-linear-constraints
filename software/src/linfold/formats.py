"""Readers for the interchange formats of computational origami.

Every reader returns a :class:`RawPattern`: points in the plane, straight
edges between them, and an assignment per edge, one of

    ``M`` mountain, ``V`` valley, ``U`` unassigned crease,
    ``F`` flat (not folded: an auxiliary line), ``B`` boundary or cut.

Supported formats:

``.fold`` (and ``.json``)
    FOLD, the JSON format of Demaine, Demaine, Ku and Lang
    (https://github.com/edemaine/fold).  Uses ``vertices_coords``,
    ``edges_vertices``, ``edges_assignment`` (or the sign of
    ``edges_foldAngle``); in a multi-frame file the crease-pattern frame is
    taken.  ``C`` (cut) is read as ``B`` and ``J`` (join) as ``F``.
``.cp``
    ORIPA / Oriedita text format, one line ``type x1 y1 x2 y2`` per segment,
    with ``1`` boundary, ``2`` mountain, ``3`` valley, ``4`` auxiliary
    and ``0`` an unassigned crease.
``.opx``
    ORIPA's XML format (``oripa.OriLineProxy`` objects).
``.svg``
    Vector drawings; the stroke colour gives the assignment (red mountain,
    blue valley, black boundary, grey auxiliary), a dashed uncoloured stroke
    is read as a valley.

The y axis of ``.cp``, ``.opx`` and ``.svg`` points down in the programs that
write them; it is flipped on input, so that all patterns are read in a
right-handed frame (a mirror image would swap nothing that matters here, but
reported coordinates then agree with the drawing up to that flip).
"""

from __future__ import annotations

import json
import math
import os
import re
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

__all__ = ["RawPattern", "FormatError", "read_pattern", "write_fold",
           "FOLDS", "ASSIGNMENTS"]

ASSIGNMENTS = ("M", "V", "U", "F", "B")
#: assignments across which the folding map reflects
FOLDS = frozenset("MVU")

Point = Tuple[float, float]


class FormatError(ValueError):
    """The file cannot be read as a crease pattern."""


@dataclass
class RawPattern:
    """A straight-line drawing with an assignment per edge."""

    vertices: List[Point]
    edges: List[Tuple[int, int]]
    assignments: List[str]
    source: str = ""
    fmt: str = ""
    meta: Dict = field(default_factory=dict)

    def bbox(self):
        xs = [p[0] for p in self.vertices]
        ys = [p[1] for p in self.vertices]
        return min(xs), min(ys), max(xs), max(ys)


class _Builder:
    """Collects segments, merging endpoints that agree to ``tol``."""

    def __init__(self, tol: float = 1e-12):
        self.tol = tol
        self.vertices: List[Point] = []
        self._grid: Dict[Tuple[int, int], List[int]] = {}
        self.edges: List[Tuple[int, int]] = []
        self.assignments: List[str] = []
        self._eindex: Dict[Tuple[int, int], int] = {}
        self.conflicts = 0

    def vertex(self, x: float, y: float) -> int:
        q = self.tol
        kx, ky = round(x / q), round(y / q)
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for i in self._grid.get((kx + dx, ky + dy), ()):
                    vx, vy = self.vertices[i]
                    if math.hypot(vx - x, vy - y) <= q:
                        return i
        self.vertices.append((float(x), float(y)))
        i = len(self.vertices) - 1
        self._grid.setdefault((kx, ky), []).append(i)
        return i

    def edge(self, u: int, v: int, a: str):
        if u == v:
            return
        a = a if a in ASSIGNMENTS else "U"
        key = (min(u, v), max(u, v))
        k = self._eindex.get(key)
        if k is None:
            self._eindex[key] = len(self.edges)
            self.edges.append(key)
            self.assignments.append(a)
            return
        old = self.assignments[k]
        if {old, a} == {"M", "V"}:
            self.conflicts += 1
        rank = {"U": 0, "F": 1, "B": 2, "M": 3, "V": 3}
        if rank[a] > rank[old]:
            self.assignments[k] = a

    def segment(self, p: Point, q: Point, a: str):
        self.edge(self.vertex(*p), self.vertex(*q), a)

    def build(self, source: str, fmt: str, meta=None, flip_y=False) -> RawPattern:
        verts = [(x, -y) if flip_y else (x, y) for x, y in self.vertices]
        meta = dict(meta or {})
        if self.conflicts:
            meta["duplicate_conflicts"] = self.conflicts
        return RawPattern(verts, list(self.edges), list(self.assignments),
                          source, fmt, meta)


# --------------------------------------------------------------------- FOLD
_FOLD_MAP = {"M": "M", "V": "V", "U": "U", "F": "F", "B": "B", "C": "B", "J": "F"}


def _fold_frame(data: dict) -> dict:
    frames = [data] + list(data.get("file_frames") or [])

    def merged(fr):
        out = dict(data)
        out.update(fr)
        return out

    def classes(fr):
        return {str(c).lower() for c in (fr.get("frame_classes") or [])}

    for fr in frames:
        if "creasepattern" in classes(fr) and merged(fr).get("vertices_coords"):
            return merged(fr)
    for fr in frames:
        m = merged(fr)
        vc = m.get("vertices_coords") or []
        if "foldedform" not in classes(fr) and vc and len(vc[0]) == 2:
            return m
    if any("foldedform" in classes(fr) for fr in frames):
        raise FormatError("this FOLD file holds only a folded form, not a crease "
                          "pattern; export the crease-pattern frame instead")
    return data


def read_fold(path: str) -> RawPattern:
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
    except json.JSONDecodeError as exc:
        raise FormatError(f"malformed FOLD/JSON: {exc}") from exc
    fr = _fold_frame(data)
    coords = fr.get("vertices_coords")
    if not coords:
        raise FormatError("the FOLD file has no vertices_coords")
    ev = fr.get("edges_vertices")
    if not ev:
        fv = fr.get("faces_vertices") or []
        if not fv:
            raise FormatError("the FOLD file has neither edges nor faces")
        seen, ev = set(), []
        for f in fv:
            for i in range(len(f)):
                e = (min(f[i], f[i - 1]), max(f[i], f[i - 1]))
                if e not in seen:
                    seen.add(e)
                    ev.append(list(e))
    ea = fr.get("edges_assignment")
    fa = fr.get("edges_foldAngle")
    b = _Builder()
    ids = [b.vertex(float(c[0]), float(c[1]) if len(c) > 1 else 0.0) for c in coords]
    for k, (u, v) in enumerate(ev):
        if ea is not None and k < len(ea) and ea[k]:
            a = _FOLD_MAP.get(str(ea[k]).upper()[:1], "U")
        elif fa is not None and k < len(fa) and fa[k] is not None:
            t = float(fa[k])
            a = "V" if t > 0 else ("M" if t < 0 else "F")
        else:
            a = "U"
        b.edge(ids[int(u)], ids[int(v)], a)
    meta = {k: fr[k] for k in ("file_title", "frame_title", "file_author",
                               "file_creator") if k in fr}
    return b.build(path, "fold", meta)


def write_fold(path: str, vertices: Sequence[Point], edges, assignments,
               title: str = "", creator: str = "linfold") -> None:
    """Write a single crease-pattern frame in FOLD 1.1."""
    doc = {
        "file_spec": 1.1,
        "file_creator": creator,
        "file_classes": ["singleModel"],
        "frame_title": title,
        "frame_classes": ["creasePattern"],
        "frame_attributes": ["2D"],
        "vertices_coords": [[float(x), float(y)] for x, y in vertices],
        "edges_vertices": [[int(u), int(v)] for u, v in edges],
        "edges_assignment": list(assignments),
    }
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(doc, fh, indent=1)
        fh.write("\n")


# ----------------------------------------------------------------------- CP
#: line types: 1 cut (the sheet edge), 2 mountain, 3 valley, 4 auxiliary.
#: ORIPA does not export its auxiliary lines to .cp, and files that use the
#: type 0 use it for creases without a mountain-valley label.
_CP_MAP = {0: "U", 1: "B", 2: "M", 3: "V", 4: "F"}


def read_cp(path: str) -> RawPattern:
    b = _Builder()
    n = 0
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            parts = line.replace(",", " ").split()
            if len(parts) < 5:
                continue
            try:
                t = int(float(parts[0]))
                x1, y1, x2, y2 = map(float, parts[1:5])
            except ValueError:
                continue
            b.segment((x1, y1), (x2, y2), _CP_MAP.get(t, "U"))
            n += 1
    if not n:
        raise FormatError("no segment could be read from the .cp file")
    return b.build(path, "cp", flip_y=True)


# ---------------------------------------------------------------------- OPX
#: ORIPA's OriLine types: 0 auxiliary, 1 cut (the sheet edge), 2 mountain,
#: 3 valley; Java's XMLDecoder omits a property at its default value (0).
_OPX_MAP = {0: "F", 1: "B", 2: "M", 3: "V", 4: "B"}


def read_opx(path: str) -> RawPattern:
    try:
        root = ET.parse(path).getroot()
    except ET.ParseError as exc:
        raise FormatError(f"malformed OPX/XML: {exc}") from exc
    b = _Builder()
    n = 0
    for obj in root.iter("object"):
        if obj.get("class") != "oripa.OriLineProxy":
            continue
        vals = {}
        for node in obj:
            prop = node.get("property")
            if prop is None:
                continue
            try:
                vals[prop] = float("".join(node.itertext()).strip())
            except ValueError:
                pass
        if not {"x0", "y0", "x1", "y1"} <= set(vals):
            continue
        b.segment((vals["x0"], vals["y0"]), (vals["x1"], vals["y1"]),
                  _OPX_MAP.get(int(vals.get("type", 0)), "U"))
        n += 1
    if not n:
        raise FormatError("no oripa.OriLineProxy found in the .opx file")
    return b.build(path, "opx", flip_y=True)


# ---------------------------------------------------------------------- SVG
_NUM = re.compile(r"[-+]?(?:\d*\.\d+|\d+\.?)(?:[eE][-+]?\d+)?")
_CMD = re.compile(r"([MmLlHhVvCcSsQqTtAaZz])")
_NAMED = {"red": "M", "crimson": "M", "blue": "V", "navy": "V", "black": "B",
          "gray": "F", "grey": "F", "green": "F"}


def _colour(c: str) -> str:
    c = (c or "").strip().lower()
    if not c or c == "none":
        return "U"
    if c in _NAMED:
        return _NAMED[c]
    rgb = None
    m = re.match(r"rgb\(\s*(\d+)[,\s]+(\d+)[,\s]+(\d+)", c)
    if m:
        rgb = tuple(int(g) for g in m.groups())
    elif c.startswith("#") and len(c) in (4, 7):
        h = c[1:] if len(c) == 7 else "".join(ch * 2 for ch in c[1:])
        try:
            rgb = tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))
        except ValueError:
            return "U"
    if rgb is None:
        return "U"
    r, g, bl = rgb
    if r > 120 and r > g + 50 and r > bl + 50:
        return "M"
    if bl > 120 and bl > g + 50 and bl > r + 50:
        return "V"
    if max(rgb) < 60:
        return "B"
    if abs(r - g) < 30 and abs(g - bl) < 30:
        return "F"
    return "U"


def _matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)]


def _transform(text: str):
    M = [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]]
    for name, args in re.findall(r"(\w+)\s*\(([^)]*)\)", text or ""):
        v = [float(t) for t in _NUM.findall(args)]
        T = [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]]
        if name == "translate":
            T[0][2] = v[0] if v else 0.0
            T[1][2] = v[1] if len(v) > 1 else 0.0
        elif name == "scale":
            T[0][0] = v[0] if v else 1.0
            T[1][1] = v[1] if len(v) > 1 else T[0][0]
        elif name == "rotate" and v:
            a = math.radians(v[0])
            c, s = math.cos(a), math.sin(a)
            cx, cy = (v[1], v[2]) if len(v) >= 3 else (0.0, 0.0)
            T = [[c, -s, cx - c * cx + s * cy], [s, c, cy - s * cx - c * cy],
                 [0.0, 0.0, 1.0]]
        elif name == "matrix" and len(v) >= 6:
            T = [[v[0], v[2], v[4]], [v[1], v[3], v[5]], [0.0, 0.0, 1.0]]
        elif name == "skewX" and v:
            T[0][1] = math.tan(math.radians(v[0]))
        elif name == "skewY" and v:
            T[1][0] = math.tan(math.radians(v[0]))
        M = _matmul(M, T)
    return M


def _apply(M, p):
    return (M[0][0] * p[0] + M[0][1] * p[1] + M[0][2],
            M[1][0] * p[0] + M[1][1] * p[1] + M[1][2])


def _path(d: str):
    """Polylines of an SVG path; curves are replaced by their chords."""
    polys, cur = [], []
    x = y = sx = sy = 0.0
    tokens = [t for t in _CMD.split(d or "") if t.strip()]
    i, cmd = 0, None
    while i < len(tokens):
        if _CMD.fullmatch(tokens[i]):
            cmd = tokens[i]
            i += 1
            nums = []
            if i < len(tokens) and not _CMD.fullmatch(tokens[i]):
                nums = [float(t) for t in _NUM.findall(tokens[i])]
                i += 1
        else:
            nums = [float(t) for t in _NUM.findall(tokens[i])]
            i += 1
        if cmd is None:
            continue
        up, rel = cmd.upper(), cmd.islower()
        if up == "Z":
            if cur:
                cur.append((sx, sy))
                polys.append(cur)
                cur = []
            x, y = sx, sy
            continue
        step = {"M": 2, "L": 2, "H": 1, "V": 1, "C": 6, "S": 4, "Q": 4,
                "T": 2, "A": 7}.get(up, 2)
        k = 0
        while k + step <= len(nums):
            ch = nums[k:k + step]
            if up == "M":
                if len(cur) > 1:
                    polys.append(cur)
                x, y = (x + ch[0], y + ch[1]) if rel else (ch[0], ch[1])
                sx, sy = x, y
                cur = [(x, y)]
                up = "L"
            elif up == "H":
                x = x + ch[0] if rel else ch[0]
                cur.append((x, y))
            elif up == "V":
                y = y + ch[0] if rel else ch[0]
                cur.append((x, y))
            else:
                ex, ey = ch[-2], ch[-1]
                x, y = (x + ex, y + ey) if rel else (ex, ey)
                cur.append((x, y))
            k += step
    if len(cur) > 1:
        polys.append(cur)
    return polys


def _length(text, default=0.0) -> Optional[float]:
    if text is None:
        return default
    t = str(text).strip()
    if t.endswith("%"):
        return None
    t = re.sub(r"(px|pt|pc|mm|cm|in|em|ex)$", "", t)
    try:
        return float(t)
    except ValueError:
        return None


def read_svg(path: str) -> RawPattern:
    try:
        root = ET.parse(path).getroot()
    except ET.ParseError as exc:
        raise FormatError(f"malformed SVG/XML: {exc}") from exc

    def collect(require_stroke: bool) -> _Builder:
        b = _Builder()

        def emit(pts, style, close=False):
            stroke = str(style.get("stroke", "")).strip().lower()
            if require_stroke and stroke in ("", "none"):
                return
            cls = str(style.get("class", "")).strip()
            if cls.upper() in ASSIGNMENTS:          # an explicit one-letter class
                a = cls.upper()
            else:
                a = _colour(stroke)
                if a == "U":
                    for key, val in (("mountain", "M"), ("valley", "V"),
                                     ("boundary", "B"), ("border", "B"),
                                     ("flat", "F"), ("aux", "F")):
                        if key in cls.lower():
                            a = val
                            break
                if a == "U" and str(style.get("stroke-dasharray", "none")) != "none":
                    a = "V"
            pts = list(pts) + ([pts[0]] if close and len(pts) > 2 else [])
            for p, q in zip(pts, pts[1:]):
                if math.hypot(q[0] - p[0], q[1] - p[1]) > 0:
                    b.segment(p, q, a)

        def walk(el, M, style):
            tag = el.tag.rsplit("}", 1)[-1]
            M = _matmul(M, _transform(el.get("transform", "")))
            style = dict(style)
            for item in (el.get("style") or "").split(";"):
                if ":" in item:
                    k_, v_ = item.split(":", 1)
                    style[k_.strip().lower()] = v_.strip()
            for attr in ("stroke", "stroke-dasharray", "class"):
                if el.get(attr) is not None:
                    style[attr] = el.get(attr)
            if tag == "line":
                v = [_length(el.get(k)) for k in ("x1", "y1", "x2", "y2")]
                if None not in v:
                    emit([_apply(M, v[0:2]), _apply(M, v[2:4])], style)
            elif tag in ("polyline", "polygon"):
                v = [float(t) for t in _NUM.findall(el.get("points", ""))]
                emit([_apply(M, (v[i], v[i + 1])) for i in range(0, len(v) - 1, 2)],
                     style, close=(tag == "polygon"))
            elif tag == "rect":
                v = [_length(el.get(k)) for k in ("x", "y", "width", "height")]
                if None not in v:
                    x0, y0, w, h = v
                    emit([_apply(M, p) for p in ((x0, y0), (x0 + w, y0),
                                                 (x0 + w, y0 + h), (x0, y0 + h))],
                         style, close=True)
            elif tag == "path":
                for poly in _path(el.get("d", "")):
                    emit([_apply(M, p) for p in poly], style)
            for child in el:
                walk(child, M, style)

        walk(root, [[1.0, 0.0, 0.0], [0.0, 1.0, 0.0], [0.0, 0.0, 1.0]], {})
        return b

    b = collect(True)
    if not b.edges:
        b = collect(False)
    if not b.edges:
        raise FormatError("no line found in the SVG file")
    return b.build(path, "svg", flip_y=True)


# ------------------------------------------------------------------ dispatch
READERS = {".fold": read_fold, ".json": read_fold, ".cp": read_cp,
           ".opx": read_opx, ".svg": read_svg}


def read_pattern(path: str) -> RawPattern:
    """Read a crease pattern, choosing the reader by the file extension."""
    ext = os.path.splitext(path)[1].lower()
    reader = READERS.get(ext)
    if reader is None:
        raise FormatError(f"unsupported file type {ext!r}; expected one of "
                          + ", ".join(sorted(READERS)))
    raw = reader(path)
    if not raw.edges:
        raise FormatError("the file contains no edge")
    return raw
