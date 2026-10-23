# Examples

Crease patterns whose answers are known, one or more for every input format. The FOLD
files are written by `make_examples.py` with the generators of `linfold.generators`;
`waterbomb_base.cp`, `preliminary_base.svg` and `kawasaki_violated.fold` come from an
earlier analyser and exercise the other readers.

```bash
linfold check triangle.fold
linfold check vertex_degree16_wrong_labels.fold --certificate cert.json --svg v16.svg
linfold verify cert.json --pattern vertex_degree16_wrong_labels.fold
```

| file | what it is | verdict | why |
|---|---|---|---|
| `triangle.fold` | three degree-four vertices (60°, 100°, 120°, 80°) around a triangle, Sec. 8 and Fig. 6(b) of the paper | not flat-foldable | the three big–little–big relations form an odd cycle; certificate of 6 rows |
| `kawasaki_violated.fold` | a degree-four vertex with 50°, 100°, 120°, 90° | not flat-foldable | Kawasaki's condition fails |
| `vertex_degree16_wrong_labels.fold` | the vertex of Fig. 3(c), labelled `MVMMVMMVMMVVVMVM` | not flat-foldable with these labels | Maekawa (`M − V = 2`), Kawasaki and big–little–big hold, but two pairs of Theorem 2 are violated; certificate of 10 rows and 2 labels |
| `vertex_45_135_135_45.fold` | Example 3, labelled `VMVV` | not flat-foldable with these labels | the labels satisfy every linear constraint (`W_lin`); only Hull's recursion, that is transitivity, rejects them, so there is no linear certificate |
| `vertex_example1.fold`, `vertex_example1.opx` | Example 1 (40°, 70°, 100°, 60°, 40°, 50°), labelled `MMMMVV` as in Fig. 2 | passes | 12 rows, three pairs; `W_lin = W_flat`, 8 assignments |
| `vertex_regular6.fold` | Example 4, six angles of 60° | passes | six taco–taco rows; `\|W_lin\| = 32`, `\|W_flat\| = 30` |
| `waterbomb_base.cp` | the waterbomb base | passes | one block of six creases; `\|W_lin\| = 32`, `\|W_flat\| = 18` |
| `preliminary_base.svg` | the preliminary base, eight angles of 45° | passes | `\|W_lin\| = 128`, `\|W_flat\| = 112` |
| `map_3x3.fold` | a 3×3 map, unassigned | passes | 12 taco–taco rows of rank 12 on 36 layer variables; `2^8` assignments survive |
| `miura_6x6.fold` | a 6×6 Miura-ori, unassigned | passes | 522 layer variables, rank 403; of `2^60` assignments `2^35` survive the relations at the 25 vertices, and the global rows remove no more |

"Passes" means that the linear constraints are consistent: whether a flat-folded state
exists then depends on transitivity, which `linfold` does not decide (see
`linfold export --format xnf` to hand the full system to a SAT solver).
