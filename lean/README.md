# Maekawa's theorem and the linear constraints of flat folding — Lean formalization

This directory contains a formalization, in Lean 4 with Mathlib, of the results of the paper

> A. Ladiana, *Maekawa's theorem and the linear constraints of flat folding*
> ([preprint](../paper/maekawa-linear-constraints-flat-folding.pdf)).

The proofs contain no `sorry` and no `native_decide`. All theorems depend only on the
standard axioms of Lean and Mathlib (`propext`, `Classical.choice`, `Quot.sound`), as
`Axioms.lean` prints.

The proofs of the paper were transcribed into Lean with the assistance of an AI system.

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.28.0) is
fixed by `lean-toolchain`, and Mathlib (v4.28.0) by `lake-manifest.json`. From the root of
the repository:

```
cd lean
lake exe cache get          # downloads the compiled Mathlib
lake build                  # about 10 minutes
lake env lean Axioms.lean   # prints the axioms of the main theorems
```

The workflow `.github/workflows/lean.yml` runs these steps on every push and fails if
`Axioms.lean` reports `sorryAx` or any axiom beyond `propext`, `Classical.choice` and
`Quot.sound`.

## The model

| Paper | Lean |
|---|---|
| Closed walk of a vertex, Eq. (4) | `Walk ι α`: a finite set `C` of creases in a linear order `ι`, read cyclically (`nxt`, `prv`), with positions `c : ι → α` in an ordered field, every crease a strict local extremum (`Walk.lean`, `Cyclic.lean`) |
| Sector `f_k` and its interval `I_k` | the sector `g` ends at the crease `g`; `lo g`, `hi g`, `len g` |
| Rows at a vertex (Lemma 1) | taken as the definition: `IsTT`, `IsTC`, `ttRows`, `tcRows`, `rows` |
| Layer variables over `𝔽₂` | `x : ι → ι → ZMod 2`, antisymmetric on `C` (`Antisymm`) |
| Mountain–valley assignment, Eq. (1) | `asg x k = x k (nxt k) + [k is a minimum]`; `1` is a valley; `mv σ = M - V` |
| Flat-folded state | `IsFlat h`: heights `h : ι → ℤ`, injective on `C`, whose layer variables `xOf h` satisfy every row (transitivity is built in) |
| `W_lin`, `W_flat`, `aff W_flat` | `Wlin`, `Wflat`, `affW` |
| Hull's recursion, `E`, `W₄`, blocks | `Chain` (crimps of maximal runs of smallest sectors, `runCrimp`), `Chain.E`, `Chain.W4`, `Chain.lab` |
| Hypergraph `H_v`, components, `γ` | `Linked`, `Conn`, `SameComp`, `gamma` |

Crimping deletes creases and keeps the names and positions of the others, so a sequence of
crimps is a sequence of subsets of one index type. As in the paper, the statements hold for
all closed walks (vertices of cones included).

## Paper ↔ Lean

| Paper | Lean name | File |
|---|---|---|
| Lemma 1 (local rows) | definitions `IsTT`, `IsTC`, `ttRows`, `tcRows` | `Walk.lean` |
| Example 1 | `example1` | `Examples.lean` |
| Lemma 2 (two rows per pair) | `card_rowsWith` | `TwoRows.lean` |
| Theorem 1 | `sum_rows_eq_vertex_row` (proof: `sum_rows_eq_vertex_row_gauge`; every row homogeneous: `eval_gauge`) | `Theorem1.lean`, `Gauge.lean` |
| Eq. (3), `M - V ≡ 2 (mod 4)` | `mv_mod_four` | `Theorem1.lean` |
| Lemma 3 (relations are components) | `lemma4`, `sum_comp_eq` | `Generic.lean`, `Components.lean` |
| Theorem 2, Eq. (5) | `theorem2`; the strengthened statement (extreme creases, maximum–minimum pairs, `M - V = 2σ(e_T)`) is `pairing` | `Generic.lean`, `Pairing.lean` |
| Example 2 | `example2`, `example2_transitive` | `Example2.lean` |
| Proposition 1 (nested pairs) | `nested` | `Nesting.lean` |
| Corollary 1 | `corollary1` | `Generic.lean` |
| Proposition 2 | `prop1` | `Rank.lean` |
| Theorem 3 (persistence) | `persistence`; the elder rule is `PersPair` (with `PersR`, `PersL`), the essential pair `Essential` | `Persistence.lean` |
| Theorem 4, blocks | `theorem3`, `card_Wlin` | `Theorem3.lean`, `Counting.lean` |
| Lemma 4 (crimping a run) | `lemma6_even`, `lemma6_odd`, `Chain.lab_eq_of_sameComp` | `Lemma6.lean`, `Hull.lean` |
| Remark 1 (Theorem 4 without Hull's theorem) | the proof of `theorem3` | `Theorem3.lean` |
| Corollary 2 | `corollary2` (see below) | `Criterion.lean` |
| Examples 3 and 4 | `example3`, `example4` | `Examples.lean` |
| Eq. (6) | `split_row` | `Perturb.lean` |
| Proposition 3 | `prop2` | `Perturb.lean` |
| Corollary 3 | `corollary3` | `Perturb.lean` |
| Proposition 4 (big–little–big) | `big_little_big` | `Generic.lean` |
| Corollary 4 | `Pattern.corollary4` | `Pattern.lean` |
| Appendix A: Eqs. (7)–(8) | `sum_ttRows`, `sum_ttRows_eq` | `Parity.lean` |
| Appendix A: Lemma 5 (parity) | `lemma2` | `Parity.lean` |
| Appendix A: third proof of Theorem 1 (one flat-folded state) | `sum_rows_eq_vertex_row_of_flat` (`exists_flat`) | `Theorem1.lean`, `Crimp.lean` |
| Appendix B: Lemma 6 (crimping a sector) | `lemma5` (at every vertex without taco–taco rows) | `Generic.lean` |
| Appendix B: proof of Proposition 1 | `nested` | `Nesting.lean` |
| Appendix B: proof of Theorem 3 | `pers_of_sameComp` (crimping, `CrimpPair`), `sameComp_of_persPair` (`persPair_unique`) | `Persistence.lean` |

The Lean names `lemma2`, `lemma4`, `lemma5` and `lemma6_*` keep the numbering of an earlier
version of the paper; the table gives the current one.

## Proofs

The formal proofs follow the paper, choosing among its routes where it gives several:

* **Theorem 1** is proved as in the paper (`Gauge.lean`): read from a lowest crease `e_B`,
  every row is homogeneous (`eval_gauge`: the sectors are ordered cyclically from the one
  after `e_B`, `gauge B a b = 0` when `a` comes first), and by Lemma 2 the sum of the rows
  keeps only the adjacent pairs, of which only the one at `e_B` is written backwards. The
  third proof of Appendix A (one flat-folded state, built by crimping and unfolding) is kept
  as `sum_rows_eq_vertex_row_of_flat`. Lemma 5 follows from Theorem 1 and Eq. (8).
* **Theorem 2** is proved as in the paper (`Pairing.lean`), at every vertex without
  taco–taco rows (`NoTC`), which include the generic ones: the extreme creases cut the sectors
  into two sides, rows keep the number of sectors of a pair on the first side (`ncls_conn`),
  so the component of `e_T` contains exactly the adjacent pairs of `e_T` and `e_B`
  (`filter_sameComp_top`); in the gauge of `e_B` the variable is constant along a component
  (`asg_add_asg`). Two steps are argued by counting rather than by following a path: every
  component contains exactly two adjacent pairs (`card_sameComp`: an even number, by
  `even_card_sameComp`, and at most two, since a connected graph with `V` vertices has at
  least `V - 1` edges), and its two creases are a maximum and a minimum (`up_iff_not_up`: the
  component has an even number of rows, and every pair other than the adjacent pair of a
  minimum has one row through its lower ends). A second proof, through Theorem 4 and Hull's
  recursion, is kept as `theorem2_hull`; the induction of Appendix B is not formalized,
  though its Lemma 6 is (`lemma5`).
* **Theorem 4** follows Remark 1 of the paper (a proof without Hull's theorem):
  `W₄ ⊆ aff W_flat ⊆ W_lin ⊆ W₄`, the first inclusion by unfolding crimps
  (`exists_lift`, `inDir_*`), the last by Lemma 3 and Lemma 4, stated as the refinement of the
  blocks by the components. Hence the components containing adjacent pairs are the blocks
  (`card_Wlin`).
* **Proposition 1** (nested pairs) is proved as in Appendix B of the paper, by induction
  with Lemma 6 (`lemma5`), which is stated here for every vertex without taco–taco rows:
  the pair of a smallest sector joins two consecutive creases, so its chord crosses no
  other, and the crimped walk keeps the other creases in their cyclic order (`Cross`
  depends only on the order of the index type).
* **Theorem 3** (persistence) is stated with the elder rule written in terms of the cyclic
  order alone (`PersPair m M`): from the minimum `e_m` one direction reaches `e_M` staying
  above `c m`, then a crease `e_y` below `c m` without rising above `c M`; the other direction
  reaches a crease `e_z` above `c M` before falling below `c m`. The essential pair is a
  highest and a lowest crease (`Essential`). The proof is that of Appendix B: by induction
  with Lemma 6, the creases of a smallest sector form a persistence pair (`persPair_consec`),
  and crimping two consecutive creases whose heights lie strictly between those of their
  outer neighbours keeps every other persistence pair (`CrimpPair.persPair`). The converse
  uses that a minimum has one persistence partner (`persPair_unique`; two maxima at the same
  height would have a taco–taco row).
* **Corollary 1 and Proposition 2** are stated for vertices without taco–taco rows (`NoTC`).
* **Proposition 3** uses the admissible perturbation of the paper, built explicitly: the new
  positions are the ranks of the key (position, type, ± size of the taco, name).
* **Corollary 4** is stated for an abstract crease pattern (`Pattern`): a walk at every
  interior vertex, a facet for every sector, and any parametrization of the layer variables.
* **Examples** are concrete walks over `Fin n` with rational positions in degrees; their
  rows, flat-folded states and explicit solutions are checked by `decide` in the kernel, and
  statements about all flat-folded states reduce to permutations of the sectors (`xOf_rank`).

## Not formalized

* The geometry behind Lemma 1: the rows are taken as definitions, and a flat-folded state is
  a layer order of the sectors that satisfies them.
* The converse in Corollary 2, which rests on Hull's enumeration of flat-foldable
  assignments. `corollary2` proves `|W_lin| = 2^(n-1-E)` and the direct implication.
* The first two proofs of Lemma 5 in Appendix A (Whitney's formula, wall crossings) and
  Remark 2; the induction of Appendix B for Theorem 2; the geometric picture of the
  Discussion (the curve of pairs of points with the same image).

## Files

| File | Content |
|---|---|
| `Cyclic.lean` | cyclic successor and predecessor in a finite set |
| `Walk.lean` | walks, intervals, rows, layer variables, assignments, flat-folded states |
| `TwoRows.lean` | Lemma 2 |
| `SumRows.lean` | the sum of the rows at symmetric variables |
| `Gauge.lean` | the gauge of a lowest crease; Theorem 1 |
| `Crimp.lean` | crimping a sector; unfolding flat-folded states; every walk has one |
| `Theorem1.lean` | Theorem 1 (both proofs), `M - V ≡ 2 (mod 4)` |
| `Parity.lean` | Eqs. (7)–(8), Lemma 5 |
| `Components.lean` | hypergraph of the rows, component equations |
| `Pairing.lean` | sides, parity of components, the row graph; Theorem 2 |
| `Nesting.lean` | Proposition 1 |
| `Persistence.lean` | Theorem 3 |
| `Run.lean`, `Hull.lean` | runs, Hull's recursion, `W₄`, blocks |
| `Lemma6.lean` | Lemma 4 |
| `Theorem3.lean`, `Counting.lean` | Theorem 4, `|W_lin| = 2^(n-1-E)`, `γ = E + 1` |
| `Generic.lean` | Lemma 3, Theorem 2, Lemma 6, Corollary 1, Proposition 4 |
| `Rank.lean` | Proposition 2 |
| `Perturb.lean` | Proposition 3, Corollary 3 |
| `Criterion.lean` | Corollary 2 |
| `Pattern.lean` | Corollary 4 |
| `Examples.lean`, `Example2.lean` | Examples 1–4 |
| `Axioms.lean` | `#print axioms` of the main theorems |

## License

Apache License 2.0 (see [`../LICENSE`](../LICENSE)), as Mathlib.
