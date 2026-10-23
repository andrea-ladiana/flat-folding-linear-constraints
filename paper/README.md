# The paper

**Maekawa's theorem and the linear constraints of flat folding**
Andrea Ladiana — Sapienza University of Rome and INdAM, Rome

[`maekawa-linear-constraints-flat-folding.pdf`](maekawa-linear-constraints-flat-folding.pdf)
is the author's preprint (the submitted version, typeset with the Springer Nature
template). It is not the version of record.

## Abstract

A flat-folded state of a crease pattern is a layer order between overlapping facets. Of
the conditions that make a layer order valid, the taco–tortilla and taco–taco constraints
are linear over 𝔽₂, while transitivity is not. We determine what the linear constraints
at a vertex say about its mountain–valley assignment. At every vertex, Maekawa's rule
modulo four is the 𝔽₂-sum of all the linear constraints there, and the assignments
induced by their solutions form the affine hull over 𝔽₂ of the flat-foldable ones:
Hull's crimping recursion with every condition read modulo four. At a generic vertex this
hull is the set of flat-foldable assignments itself. There the taco–tortilla constraints
pair up the creases, forcing equal assignments on the two creases at the extreme rays of
the folded image and opposite ones on every other pair, so that every solution,
transitive or not, satisfies Maekawa's rule M − V = ±2 on the numbers of mountain and
valley creases. The pairs are the persistence pairs of the folded angle, read as a height
function around the vertex, and Hull's recursion cancels them in order of increasing
persistence. The proofs read the layer order from an extreme crease, where every
constraint becomes homogeneous, and rest on one structural fact: every overlapping pair
of non-adjacent sectors occurs in exactly two constraints, and every adjacent pair in
one. They do not use Maekawa's theorem, and prove it anew, with transitivity entering
only to order the folds that coincide in the folded image.

## Where the results are implemented and formalized

| result | software (`../software`) | Lean (`../lean`) |
|---|---|---|
| Lemma 1, local rows | `Vertex.rows` | definitions `IsTT`, `IsTC` |
| Lemma 2, two rows per pair | `Vertex.pair_multiplicities` | `card_rowsWith` |
| Theorem 1, sum of the rows | `Vertex.theorem1_holds` | `sum_rows_eq_vertex_row` |
| Lemma 3, components | `Vertex.components`, `Vertex.relations` | `lemma4` |
| Theorem 2, pairing | `Vertex.pairs` | `pairing`, `theorem2` |
| Theorem 3, persistence | `Vertex.persistence_pairs` | `persistence` |
| Theorem 4, affine hull | `Vertex.hull`, `Vertex.theorem4_holds` | `theorem3`, `card_Wlin` |
| Corollary 2 | `HullRecursion.linear_equals_flat` | `corollary2` (direct implication) |
| Corollary 4, certificates | `linfold check`, `linfold verify` | `Pattern.corollary4` |

The full correspondences are in [`../software/docs/theory.md`](../software/docs/theory.md)
and [`../lean/README.md`](../lean/README.md).

## Citation

```bibtex
@misc{Ladiana2026Maekawa,
  author = {Ladiana, Andrea},
  title  = {Maekawa's theorem and the linear constraints of flat folding},
  year   = {2026},
  note   = {Preprint},
  url    = {https://github.com/andrea-ladiana/flat-folding-linear-constraints}
}
```

## Copyright

© 2026 Andrea Ladiana. The paper is not covered by the Apache License of the software
and of the formalization in this repository.
