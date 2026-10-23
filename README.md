# Maekawa's theorem and the linear constraints of flat folding

[![software](https://github.com/andrea-ladiana/flat-folding-linear-constraints/actions/workflows/software.yml/badge.svg)](https://github.com/andrea-ladiana/flat-folding-linear-constraints/actions/workflows/software.yml)
[![lean](https://github.com/andrea-ladiana/flat-folding-linear-constraints/actions/workflows/lean.yml/badge.svg)](https://github.com/andrea-ladiana/flat-folding-linear-constraints/actions/workflows/lean.yml)
[![license](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

The paper, its formalization in Lean 4, and the software that implements it.

A flat-folded state of an origami crease pattern is a layer order between overlapping
facets. Two of the three families of conditions on a layer order, the taco–tortilla and
taco–taco constraints, are linear over 𝔽₂; the third, transitivity, is not, and is where
the NP-hardness of flat foldability lies. The paper determines exactly what the linear
constraints at a vertex say about its mountain–valley assignment:

* **Theorem 1.** At every vertex, Maekawa's rule modulo four is the 𝔽₂-sum of all the
  linear constraints there.
* **Theorem 2.** At a generic vertex the taco–tortilla constraints pair up the creases:
  the two creases at the extreme rays of the folded image are forced equal, every other
  pair opposite. Hence every solution, transitive or not, has `M − V = ±2`.
* **Theorem 3.** The pairs are the persistence pairs of the folded angle, read as a
  height function around the vertex.
* **Theorem 4.** At every vertex the assignments allowed by the linear constraints form
  the affine hull over 𝔽₂ of the flat-foldable ones: Hull's crimping recursion read
  modulo four.

The proofs give a new proof of Maekawa's theorem, in which transitivity is used only to
order the folds that coincide in the folded image.

## Contents

| folder | what it holds |
|---|---|
| [`paper/`](paper) | the preprint (PDF), its abstract and how to cite it |
| [`lean/`](lean) | a formalization of the results in Lean 4 with Mathlib: no `sorry`, standard axioms only, every numbered result of the paper mapped to a Lean theorem |
| [`software/`](software) | **`linfold`**, a pure-Python tool and library that applies the theory to crease patterns: rows, pairs and blocks at every vertex, the linear system of the whole pattern, certificates of non-flat-foldability, and their verification |

## linfold in one minute

```bash
pip install "git+https://github.com/andrea-ladiana/flat-folding-linear-constraints#subdirectory=software"

linfold vertex 40 70 100 60 40 50                 # Example 1 of the paper, from its angles
linfold check pattern.fold --certificate cert.json --svg pattern.svg
linfold verify cert.json --pattern pattern.fold   # check a certificate independently
```

`linfold check` reads FOLD, ORIPA (`.cp`, `.opx`) and SVG crease patterns. Before any
search for a layer order it solves the linear constraints by Gaussian elimination: when
they are inconsistent the pattern cannot fold flat, and `linfold` returns a short,
independently checkable certificate (for the classical triangle pattern, the six rows of
three big–little–big lemmas). It tests the mountain–valley labels of the file, reports the
labels that the constraints force, and exports the whole system for SAT solvers. See
[`software/README.md`](software/README.md).

## The Lean formalization

```bash
cd lean
lake exe cache get && lake build
lake env lean Axioms.lean        # propext, Classical.choice, Quot.sound only
```

The formalization takes the rows of Lemma 1 as definitions and covers every numbered
result of the paper except the converse in Corollary 2, which rests on Hull's enumeration;
[`lean/README.md`](lean/README.md) maps the paper to the Lean names and lists the routes
taken where the paper gives several proofs. Continuous integration rebuilds it and audits
its axioms on every change.

## Citation

If you use this work, please cite the paper:

```bibtex
@misc{Ladiana2026Maekawa,
  author = {Ladiana, Andrea},
  title  = {Maekawa's theorem and the linear constraints of flat folding},
  year   = {2026},
  note   = {Preprint},
  url    = {https://github.com/andrea-ladiana/flat-folding-linear-constraints}
}
```

GitHub's *Cite this repository* button gives the same data from
[`CITATION.cff`](CITATION.cff).

## License

The software and the formalization are released under the Apache License 2.0
([`LICENSE`](LICENSE)). The paper in [`paper/`](paper) is © 2026 Andrea Ladiana and is not
covered by that license.

## Use of AI tools

The proofs of the paper were transcribed into Lean, and the software was written, with the
assistance of an AI system.

## Contact

Andrea Ladiana — Department of Basic and Applied Sciences for Engineering, Sapienza
University of Rome — andrea.ladiana@uniroma1.it
