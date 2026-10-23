# From the paper to the code

This page fixes the conventions of `linfold` and maps the results of

> A. Ladiana, *Maekawa's theorem and the linear constraints of flat folding*

to the functions that compute them. Section, equation and theorem numbers refer to the
[preprint](../../paper/maekawa-linear-constraints-flat-folding.pdf).

## Layer variables and assignments

For two facets `f_i`, `f_j` whose folded images overlap, the layer variable is
`x_ij ∈ 𝔽₂`, with `x_ij = 0` when `f_i` lies above `f_j` (the paper's `r_ij = +1`), and
`x_ji = x_ij + 1`. Every facet shows one side of the paper once folded, `p_i = ±1`, with
`p_i = −p_j` across every crease. The assignment of the crease `e_ij` is (Eq. (1))

```
sigma(e_ij) = p_i r_ij        (+1 mountain, -1 valley)
```

and in bits, with `s = 0` for a mountain and `s = 1` for a valley,
`s(e_ij) = x_ij + [p_i = −1]`. `linfold` uses this formula for every assignment of the
layer variables, transitive or not.

A row is an equation `sum of terms = 0` whose terms are oriented layer variables
([`linfold.rows.Row`](../src/linfold/rows.py)):

| family | condition | row |
|---|---|---|
| taco–tortilla `TT(e_ij, f_k)` | the image of `f_k` covers a segment of the image of `e_ij` in its interior | `x_ik + x_jk = 0` |
| taco–taco `TC(e_ij, e_kl)` | the images of the two creases overlap in a segment, and the four facets have a common region | `x_ik + x_jk + x_il + x_jl = 0` |

`Row.equation()` writes every variable with the smaller index first; each reversed
variable adds 1 to the constant.

## A single vertex

[`linfold.vertex.Vertex`](../src/linfold/vertex.py) takes the sector angles
`alpha_1, ..., alpha_n` in cyclic order. In the code, indices are 0-based: sector `i` lies
between the creases `i − 1` and `i`, and crease `i` separates the sectors `i` and `i + 1`.
Printed names are 1-based, as in the paper. The walk (Eq. (4)) is `Vertex.pos`, with the
last crease at position 0; crease `k` is a maximum when `pos[k] > pos[k − 1]`. Angles may
be integers, fractions or floats; floats are compared with the tolerance `tol`.

| paper | code |
|---|---|
| Lemma 1 (local rows) | `Vertex.rows`, `tt_rows`, `tc_rows` |
| generic vertex | `Vertex.generic` |
| Lemma 2 (two rows per pair) | `Vertex.pair_multiplicities()` |
| vertex row, Eq. (2) | `Vertex.vertex_row()` |
| Theorem 1 | `Vertex.theorem1_holds()`; its proof (every row homogeneous when numbered from a lowest crease): `Vertex.gauge_homogeneous()` |
| hypergraph `H_v`, components, `γ(v)` | `Vertex.components`, `Vertex.gamma` |
| Lemma 3 (`W_lin`, its equations) | `Vertex.relations`, `dim_wlin`, `wlin_count`, `wlin_words()` |
| Theorem 2 (pairs) | `Vertex.pairs`, each with its path of rows; extreme creases `Vertex.top`, `Vertex.bottom` |
| Proposition 1 (nesting) | `Vertex.nested()` |
| Proposition 2 (rank `N − m − c`) | `Vertex.rank()`, `Vertex.cycles` |
| Theorem 3 (persistence) | `Vertex.persistence_pairs()` |
| Proposition 4 (big–little–big) | `Vertex.big_little_big()` |
| crimping, `E(v)`, Hull's recursion, blocks | `Vertex.hull` ([`linfold.hull`](../src/linfold/hull.py)): `crimps`, `blocks`, `E`, `flat_count` |
| Theorem 4 (`W_lin = aff W_flat = W_4`, `γ = E + 1`) | `Vertex.theorem4_holds()`; `HullRecursion.test(sigma, mod4=True)` decides membership in `W_4` |
| Corollary 2 | `HullRecursion.linear_equals_flat` |
| Corollary 3 (Maekawa) and Hull's characterisation of `W_flat` | `Vertex.check(word)` |

`Vertex.verify_theorems()` checks Lemma 2, Theorem 1, Theorem 4 and, at vertices without
taco–taco rows, Theorems 2 and 3 and Proposition 1, by comparing independent
computations; it raises `InternalError` on a mismatch. The command `linfold vertex` runs
it on every input.

A relation is printed as a parity of valleys: on a block of `L` creases,
`sum of s = parity` is the same as `M − V ≡ L − 2·parity (mod 4)`. For a pair it reads
*equal* (parity 0) or *opposite* (parity 1).

## A crease pattern

[`linfold.pattern.CreasePattern`](../src/linfold/pattern.py) is built from a planar
subdivision ([`linfold.planar`](../src/linfold/planar.py)): every crossing is split, points
closer than `1e-7` (on the unit-size drawing) are welded, the faces are recovered by a
half-edge walk, and faces separated by auxiliary lines are merged into facets. Facets and
creases are numbered from 0. A crease is a pair of facets separated by folded edges;
collinear edges between the same two facets are one crease, with one layer variable.

Every interior vertex becomes a `Vertex` whose sectors are facets and whose creases are
creases of the pattern, so its rows (`CreasePattern.local_rows`) are rows of the whole
pattern. The relations of all vertices form the **local system**
([`linfold.analysis`](../src/linfold/analysis.py)), on one bit per crease. Two convex
facets that share two vertices share the segment between them, which is then a crease of
both; so the overlapping pairs of non-adjacent sectors at different vertices are
different, the local rows of different vertices share only crease variables, and the
local system is exactly the projection on the creases of all the rows at all vertices.

The **global system** (`CreasePattern.folding.rows`) is found from the folded polygons:
the folding map reflects across every crease, the overlaps are the pairs of convex facet
images that meet in positive area, a TT row is a crease image crossing the interior of a
facet image, a TC row a pair of collinear crease images whose four facets have a common
region. These predicates use explicit line arithmetic with the tolerances of
[`linfold.geometry`](../src/linfold/geometry.py). At a vertex, the global rows whose
creases and facets are incident to it are exactly the rows of Lemma 1, a fact that the
tests check on random vertices and that `linfold check` uses to warn about imprecise
coordinates.

Corollary 4 of the paper (the vertex rows change neither the rank nor the solutions of
the global system) is checked on every pattern and reported.

## Linear algebra over 𝔽₂

[`linfold.f2.AffineSystem`](../src/linfold/f2.py) stores each row as a Python integer
used as a bit set, so that adding two rows is one XOR. `solve()` returns the rank,
consistency and free variables; `Solution.form(c)` writes a variable as an affine form in
the free ones (constant: the variable is forced); `projection_rank(cols)` is the
dimension of the projection of the solution space, which counts the mountain–valley
assignments induced by the solutions. An inconsistent system yields a certificate by a
second elimination that tracks which input rows were added, followed by a deletion pass
that makes it inclusion-minimal.
