# linfold

**The linear constraints of flat folding**, computed. `linfold` reads an origami crease
pattern (FOLD, ORIPA `.cp`/`.opx`, SVG) or the angles of a single vertex, writes the
taco–tortilla and taco–taco constraints on its layer order as a linear system over
𝔽₂, and reports what the paper

> A. Ladiana, *Maekawa's theorem and the linear constraints of flat folding*
> ([preprint](../paper/maekawa-linear-constraints-flat-folding.pdf))

proves they say about the pattern and its mountain–valley assignment.

* **Polynomial pre-filter.** The linear system is solved by Gaussian elimination. If it
  is inconsistent, the pattern certainly cannot fold flat, and no search for a layer
  order (an NP-hard problem in general) is needed.
* **Certificates of non-flat-foldability.** An inconsistency comes with a short list of
  constraints whose left-hand sides cancel and whose constants add up to 1: a proof
  that anyone can check by adding bits. For the classical triangle pattern it is the
  six rows of the three big–little–big lemmas. `linfold verify` checks a certificate
  against the pattern file.
* **Search-space reduction.** At every vertex the constraints pair up the creases (one
  pair forced equal, the others forced opposite) or, at degenerate vertices, group them
  into blocks of prescribed parity. `linfold` reports these relations, the number of
  mountain–valley assignments that survive them, the labels they force, and the
  dimension of the space of layer orders left for a solver.

The package is pure Python (3.9+), with no dependencies.

## Installation

```bash
pip install "git+https://github.com/andrea-ladiana/flat-folding-linear-constraints#subdirectory=software"
```

or, from a clone of the repository,

```bash
cd software
pip install -e ".[test]"
python -m pytest
```

## Quick start

### A single vertex

```bash
linfold vertex 45 135 135 45 --mv VMVV
```

```text
Rows (Lemma 1): 2 taco-tortilla, 1 taco-taco, on 6 overlapping pairs of sectors; rank 3
  TT(e4, f2): x[f4,f2] + x[f1,f2] = 0
  TT(e4, f3): x[f4,f3] + x[f1,f3] = 0
  TC(e1, e3): x[f1,f3] + x[f2,f3] + x[f1,f4] + x[f2,f4] = 0

Theorem 1   sum of all rows = vertex row (Maekawa mod 4): yes
Lemma 3     1 component(s) with adjacent pairs: dim W_lin = 4 - 1 = 3, |W_lin| = 8
Relations   {e1, e2, e3, e4}: odd number of valleys (M - V = 2 mod 4)

Hull's recursion (Sec. 7): 1 crimp(s), E = 0 with k even
  angle 45: run of 2 sector(s), creases e3, e4, e1 -> e*1  (M - V = +-1)
  final walk: e2, e*1  (M - V = +-2)
Theorem 4   W_lin = aff W_flat = W_4, dim 3; blocks = components: yes
Corollary 2 |W_flat| = 6 (Hull), |W_lin| = 8: transitivity is needed here

Assignment  VMVV:  M - V = -2
  Maekawa mod 4: yes;  Maekawa: yes;  big-little-big: yes
  induced by a solution of the rows (in W_lin): yes
  flat-foldable (Hull): NO
    crimping the sectors of angle 45: creases e3, e4, e1 have M - V = -3, not +1 or -1
```

Angles are in degrees, in cyclic order, and read exactly (`22.5` and `45/2` are the same
number), so coincidences between crease rays are exact. Crease `e_k` separates the sectors
`f_k` and `f_{k+1}`. `--list` prints all the assignments in `W_lin` and `W_flat`, `--svg`
draws the walk with its pairs, `--json` gives everything in machine-readable form, and
`--cone` accepts walks whose angles do not add up to 360°.

### A crease pattern

```bash
linfold check examples/triangle.fold --certificate cert.json --svg triangle.svg
```

```text
Pattern   7 facets, 9 creases (0 M, 0 V, 9 unassigned), 3 interior vertices
Verdict   NOT FLAT-FOLDABLE
          the relations at the vertices are inconsistent (local linear certificate)

Vertices
  v0 (0, 1)  degree 4
      generic; rows 4 TT + 0 TC; components gamma = 2; |W_lin| = 2^2 = 4, |W_flat| = 4
      relations: c6, c8 opposite [big-little-big]; c5, c7 equal [extreme]
  ...

Local system: the relations at the vertices, one bit per crease
  9 creases, 6 relations (sums of 12 rows), rank 5: INCONSISTENT

Global system: all taco-tortilla and taco-taco rows of the folded pattern
  21 layer variables, 33 TT + 0 TC rows, rank 20: INCONSISTENT
  Corollary 4: the vertex rows change neither rank nor solutions: yes

Certificate: 6 equations (local) prove that the pattern has no flat-folded state
  at vertex v0 (0, 1): c6, c8 opposite
      TT(c6, F5): x[F6,F5] + x[F3,F5] = 0
      TT(c8, F3): x[F5,F3] + x[F6,F3] = 0
  at vertex v1 (-0.866025, -0.5): c3, c8 opposite
      ...
  sum of all left-hand sides: 0;  sum of the constants: 1
```

Creases are named `c0, c1, ...` and facets `F0, F1, ...`; `--format json` lists their
coordinates. When the file assigns mountains and valleys, they are tested too: against
Maekawa's rule and Hull's recursion at every vertex, and against the local and global
systems, which yields a certificate when the labels are wrong even though every local rule
holds (see `examples/vertex_degree16_wrong_labels.fold`).

| option | effect |
|---|---|
| `--certificate FILE` | write the certificate (JSON) |
| `--svg FILE` | draw the pattern, the forced labels and the certificate |
| `--complete FILE` | write a FOLD file in which the labels forced by the constraints are filled in |
| `--format text\|markdown\|json` | output format |
| `--local` | skip the global system (no folding of the polygons) |
| `--ignore-labels` | analyse the geometry only |
| `--angle-tol`, `--kawasaki-tol` | tolerances in radians (defaults `1e-6`, `1e-4`) |

### Certificates

```bash
linfold verify cert.json                          # the algebra: the equations add up to 0 = 1
linfold verify cert.json --pattern triangle.fold  # and each equation is a constraint of the pattern
```

A certificate locates facets, creases and vertices by points in the coordinates of the
file, so it does not depend on the numbering used by `linfold`. The format, and how to
check one by hand, are described in [docs/certificates.md](docs/certificates.md).

### Exporting the system

```bash
linfold export pattern.fold -o system.json            # variables, rows, transitivity triples
linfold export pattern.fold -o system.cnf --format xnf
```

The XNF file is CNF with XOR clauses, the input format of
[CryptoMiniSat](https://github.com/msoos/cryptominisat): the linear rows become XOR
clauses and transitivity two ordinary clauses per triple of facets with a common region.
For patterns with convex facets these constraints characterise the flat-folded states
(Akitaya, Demaine and Ku), so the formula is satisfiable exactly when the pattern folds
flat, and the solver receives the linear part in the form it eliminates best.

## What is computed

At every interior vertex, from the angles alone (Secs. 3–7 of the paper):

| quantity | paper |
|---|---|
| the walk `c_k` (crease rays in the folded image) | Eq. (4) |
| taco–tortilla and taco–taco rows | Lemma 1 |
| sum of the rows = vertex row (Maekawa's rule mod 4) | Theorem 1 |
| components of the hypergraph of the rows; `dim W_lin = n − γ` | Lemma 3 |
| at vertices without taco–taco rows: the pairs, one equal and `m − 1` opposite | Theorem 2 |
| the pairs as persistence pairs of the walk; nesting | Theorem 3, Proposition 1 |
| rank of the rows `N − m − c` | Proposition 2 |
| big–little–big pairs and their two rows | Proposition 4 |
| Hull's recursion, `E`, the blocks, `W_lin = aff W_flat = W_4` | Theorem 4 |
| `\|W_flat\|` (Hull's count) and whether `W_lin = W_flat` | Corollary 2 |

On the whole pattern:

* the **local system**: the relations of all the vertices, one bit per crease. It is the
  exact projection of all the rows at all the vertices on the creases, since two convex
  facets that are not adjacent meet in at most one vertex;
* the **global system**: every taco–tortilla and taco–taco row of the folded pattern,
  found from the folded polygons, on the layer variables of all overlapping pairs; its
  rank, the dimension of its projection on the creases, and the check of Corollary 4
  (the vertex rows change neither rank nor solutions).

[docs/theory.md](docs/theory.md) gives the conventions and maps every function to the
paper.

## Python API

```python
from linfold import Vertex, load, analyze

v = Vertex([40, 70, 100, 60, 40, 50])     # Example 1 of the paper
v.rows                                    # 12 taco-tortilla rows
[(p.creases, p.equal) for p in v.pairs]   # [((0, 5), False), ((1, 2), True), ((3, 4), False)]
v.persistence_pairs()                     # the same pairs, from the walk alone
v.wlin_count, v.wflat_count               # (8, 8)
v.check("MMMMVV").flat_foldable           # True

report = analyze(load("pattern.cp"))
report.verdict                            # 'passes', 'not-flat-foldable', 'labels-not-flat-foldable'
report.local.mv_dim, report.global_.mv_dim
report.certificate                        # None, or a Certificate
```

Indices are 0-based in the API and 1-based in printed vertex output (`e1`, `f1`), as in
the paper.

## Conventions and limits

* **Labels.** Mountain is `+1`, valley `-1`. `M`, `V` and `U` (unassigned) edges are
  creases; `F` (flat, auxiliary) edges are not folded, and the faces on their two sides
  form one facet; `B` is the boundary. In `.cp` files the types are 1 boundary, 2
  mountain, 3 valley, 4 auxiliary and 0 unassigned.
* **Tolerances.** Patterns are brought to unit size. Two crease rays at a vertex coincide
  when they are closer than `--angle-tol` in the folded image; Kawasaki's alternating sum
  may deviate from zero by `--kawasaki-tol`. The global rows are found from the folded
  polygons independently of the angles; if the rows of a vertex are missing from them,
  the report warns that the coordinates are too imprecise.
* **Necessary conditions.** The linear constraints are necessary for flat foldability.
  When they are consistent, transitivity decides, and that is the NP-hard part of the
  problem (Bern–Hayes); `linfold` does not search for layer orders.
* **Convex facets.** The constraints of the paper assume convex facets, where the
  tortilla–tortilla constraints are absent. The global system is skipped, with a
  message, when a facet is not convex.

Exit status: `0` when no obstruction is found, `2` when the pattern, or the pattern with
its labels, is proved not flat-foldable, `1` on an input error.

## How it is tested

`python -m pytest` runs about 900 tests in a few seconds. They check every number stated
in the examples of the paper, and on hundreds of random vertices (generic, and with angles
on a lattice so that coincidences are exact) they compare computations that the paper
proves equal but the code performs independently:

* the components of the hypergraph against Gaussian elimination (Lemma 3);
* the pairs against the persistence pairs of the walk (Theorems 2 and 3);
* the flat-foldable assignments from all layer orders against Hull's recursion, and
  their affine hull against the relations (Theorem 4, Corollary 2);
* the rows of a vertex computed from its angles against the rows found from the folded
  polygons;
* the number of flat-folded states against a brute-force count of the exported XNF
  formula.

`LINFOLD_TEST_SCALE=20 python -m pytest` multiplies the number of random vertices by 20.
The global rows were also compared, overlap by overlap and row by row, with an independent
implementation based on the Shapely geometry library, on map folds, Miura-ori, pleats, the
waterbomb and preliminary bases and single vertices.

## Related software

[Flat-Folder](https://github.com/origamimagiro/flat-folder) (J. Ku) computes all the
flat-folded states of a crease pattern; [ORIPA](https://github.com/oripa/oripa) and
[Oriedita](https://github.com/oriedita/oriedita) are crease-pattern editors; the
[FOLD](https://github.com/edemaine/fold) format is the common interchange format. `linfold`
does not search for layer orders: it implements the linear layer of the problem and the
local theory of the paper, and is meant to run before such tools, or inside them.

## License and citation

Apache License 2.0. If you use `linfold`, please cite the paper; see
[`CITATION.cff`](../CITATION.cff) at the root of the repository.
