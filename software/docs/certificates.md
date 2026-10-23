# Certificates of non-flat-foldability

A `linfold` certificate is a list of equations over 𝔽₂, each of them satisfied by every
flat-folded state of the pattern, whose left-hand sides cancel and whose constants add up
to 1. No assignment of the layer variables satisfies all of them, so no flat-folded state
exists. This is the parity certificate of Corollary 4 of the paper; Nakajima's cycle
certificates are the same objects at vertices without taco–taco rows.

## The equations

Each item is one of:

* a **taco–tortilla row** `TT(e_ij, f_k)`: `x_ik + x_jk = 0`;
* a **taco–taco row** `TC(e_ij, e_kl)`: `x_ik + x_jk + x_il + x_jl = 0`;
* an **assignment fact**, when the claim is about the labelled pattern: the crease `e_ij`
  (with `i < j`) carries the label of the file, so `x_ij = s + [p_i = −1]`, where `s = 0`
  for a mountain, `s = 1` for a valley and `p_i = ±1` is the side of `f_i` (Eq. (1) of
  the paper).

Here `x_ab = 0` means that `f_a` lies above `f_b`, and `x_ba = x_ab + 1`.

## The JSON format

```json
{
  "format": "linfold-certificate",
  "version": 1,
  "claim": "pattern",
  "level": "local",
  "statement": "The equations below hold in every flat-folded state of the pattern. ...",
  "pattern": {"name": "triangle.fold", "file": "triangle.fold", "sha256": "..."},
  "facets":   {"1": {"point": [0.60606369987, -2.3]}, "...": {}},
  "creases":  {"3": {"facets": [1, 6], "midpoint": [0.0, -0.5], "label": "U"}, "...": {}},
  "vertices": {"0": {"point": [0.0, 1.0]}, "...": {}},
  "items": [
    {"kind": "TT", "creases": [6], "tortilla": 5, "terms": [[6, 5], [3, 5]],
     "vertex": 0, "equation": {"pairs": [[3, 5], [5, 6]], "rhs": 1}},
    "..."
  ],
  "relations": [{"vertex": 0, "creases": [6, 8], "valley_parity": 1, "items": [0, 1]}],
  "sum": {"pairs": [], "rhs": 1}
}
```

* `claim` is `pattern` (no flat-folded state at all) or `assignment` (none with the labels
  of the file).
* `level` is `local` (every row lies at a vertex, and the rows are grouped into the
  relations they add up to, in `relations`) or `global`.
* `facets`, `creases` and `vertices` give, in the coordinates of the file, a point inside
  each facet, the facets and the midpoint of each crease, and the position of each
  vertex. The numbers used in `items` are only labels for these objects.
* Each item states its `terms` as ordered pairs of facets, as the definition of the row
  writes them, and its `equation` in canonical form: the pairs `[a, b]` with `a < b` that
  occur an odd number of times, and the constant `rhs`, which counts the reversed terms.

## Checking a certificate

`linfold verify cert.json` does the algebra: it recomputes each canonical equation from
its terms and adds them all up. `linfold verify cert.json --pattern FILE` also locates
every facet, crease and vertex in the file by its point, recomputes the rows of the
pattern from its geometry (at the stated vertex from the angles, otherwise from the
folded polygons), and checks that every item is one of them; that every assignment fact
agrees with the label in the file; and that the sides `p_i` used by the facts come from a
two-colouring of the facets, up to turning the whole sheet over (which changes an even
number of constants and leaves the sum unchanged).

## By hand: the triangle pattern

The certificate of `examples/triangle.fold` has six rows, two at each corner of the
triangle; the facet `F6` is the triangle, `F1`, `F3`, `F5` the facets beyond its edges,
and `c3`, `c6`, `c8` its edges. At the corner `v0` the triangle is the smallest sector,
and the two rows of the big–little–big lemma (Proposition 4) are

```
TT(c6, F5): x[F6,F5] + x[F3,F5] = 0        canonical:  x[3,5] + x[5,6] = 1
TT(c8, F3): x[F5,F3] + x[F6,F3] = 0        canonical:  x[3,5] + x[3,6] = 0
```

(a reversed variable, such as `x[F6,F5] = x[5,6] + 1`, adds 1 to the constant). Their
sum is `x[3,6] + x[5,6] = 1`: the layer variables of the two triangle edges at `v0`,
`c6` (between `F3` and `F6`) and `c8` (between `F5` and `F6`), differ. Since `F3` and
`F5` show the same side of the paper, Eq. (1) turns this into opposite assignments of
the two creases. The other two corners give `x[1,6] + x[5,6] = 1` and
`x[1,6] + x[3,6] = 1`. Adding the three relations, every variable occurs twice and the
constants add up to `1 + 1 + 1 = 1`: the three edges of the triangle cannot be pairwise
opposite.
