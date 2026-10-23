#!/usr/bin/env python3
"""Write the example crease patterns of this folder (FOLD files).

    python make_examples.py

The ``.cp``, ``.opx`` and ``.svg`` examples are kept as they are: they
exercise the other readers.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "src"))

from linfold import generators as gen          # noqa: E402

EXAMPLES = [
    ("triangle.fold", gen.triangle(),
     "Three degree-four vertices around a triangle (Sec. 8 of the paper)"),
    ("vertex_example1.fold", gen.single_vertex([40, 70, 100, 60, 40, 50], "MMMMVV"),
     "The vertex of Example 1, with the labels of Fig. 2"),
    ("vertex_degree16_wrong_labels.fold",
     gen.single_vertex([39, 29, 19, 10, 6, 10, 45, 46, 26, 14, 8, 12, 27, 42, 10, 17],
                       "MVMMVMMVMMVVVMVM"),
     "The vertex of Fig. 3(c), with labels that satisfy Maekawa, Kawasaki and "
     "big-little-big but are not flat-foldable"),
    ("vertex_45_135_135_45.fold", gen.single_vertex([45, 135, 135, 45], "VMVV"),
     "Example 3: labels allowed by every linear constraint, not flat-foldable"),
    ("vertex_regular6.fold", gen.single_vertex([60] * 6),
     "Example 4: the regular vertex of degree six"),
    ("miura_6x6.fold", gen.miura(6, 6), "A Miura-ori, creases unassigned"),
    ("map_3x3.fold", gen.grid(3, 3), "A 3x3 map, creases unassigned"),
]


def write_opx(path, segs):
    """ORIPA's XML format (y axis pointing down, as ORIPA writes it)."""
    code = {"B": 1, "M": 2, "V": 3, "F": 0}
    out = ['<?xml version="1.0" encoding="UTF-8"?>',
           '<java version="1.8.0" class="java.beans.XMLDecoder">',
           ' <object class="oripa.DataSet">',
           '  <void property="lines">',
           f'   <array class="oripa.OriLineProxy" length="{len(segs)}">']
    for i, ((x0, y0), (x1, y1), a) in enumerate(segs):
        out += [f'    <void index="{i}">', '     <object class="oripa.OriLineProxy">',
                f'      <void property="type"><int>{code[a]}</int></void>']
        for prop, val in (("x0", x0), ("x1", x1), ("y0", -y0), ("y1", -y1)):
            out.append(f'      <void property="{prop}"><double>{val:.15g}</double></void>')
        out += ['     </object>', '    </void>']
    out += ['   </array>', '  </void>', ' </object>', '</java>', '']
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(out))


def main():
    for name, segs, title in EXAMPLES:
        gen.write_segments(os.path.join(HERE, name), segs, title)
        print("wrote", name)
    write_opx(os.path.join(HERE, "vertex_example1.opx"),
              gen.single_vertex([40, 70, 100, 60, 40, 50], "MMMMVV"))
    print("wrote vertex_example1.opx")


if __name__ == "__main__":
    main()
