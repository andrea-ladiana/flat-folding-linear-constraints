import Origami.Crimp
import Origami.Gauge

/-!
# Theorem 1: the vertex row is the sum of all the rows

For every closed walk (in particular for every interior vertex, degenerate or not), and
identically in the layer variables,

  `∑_{rows r} r.eval x = ∑_k x k (nxt k) + 1`,

i.e. as affine equations over `𝔽₂` the vertex row `∑_k x_{k,k+1} = 1` is the sum of all the
taco–tortilla and taco–taco rows at the vertex.

**Proofs in the formalization.**  The main proof is the one of the paper
(`sum_rows_eq_vertex_row_gauge`, in `Gauge.lean`): read from a lowest crease, every row is
homogeneous, and Lemma 2 leaves only the adjacent pairs, one of them reversed.  We keep a
second proof, `sum_rows_eq_vertex_row_of_flat`, which is one of the alternative proofs of the
paper's appendix: the linear parts agree by Lemma 2 (`sum_rows_add_vertex_eq`), and the
constant is read on the flat-folded state constructed by repeated crimps (`exists_flat`).
Lemma 5 (the parity of `S + D`) follows in `Parity.lean`.  None of these routes uses
Maekawa's theorem.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-- At a walk with two creases there is no row, and the vertex row holds identically. -/
lemma sum_rows_eq_vertex_row_two {x : ι → ι → ZMod 2} (hx : w.Antisymm x)
    (h2 : w.C.card = 2) : ∑ r ∈ w.rows, r.eval x = ∑ k ∈ w.C, x k (nxt w.C k) + 1 := by
  rw [rows_eq_empty_of_two h2, Finset.sum_empty, sum_nxt_two h2 hx]; decide

/-- **Theorem 1.**  The sum of all the rows at a vertex is its vertex row, identically in the
(antisymmetric) layer variables.  Proof: the gauge of a lowest crease (`Gauge.lean`). -/
theorem sum_rows_eq_vertex_row {x : ι → ι → ZMod 2} (hx : w.Antisymm x) :
    ∑ r ∈ w.rows, r.eval x = ∑ k ∈ w.C, x k (nxt w.C k) + 1 := by
  by_cases h2 : w.C.card = 2
  · exact sum_rows_eq_vertex_row_two hx h2
  exact sum_rows_eq_vertex_row_gauge hx (by have := w.two_le; omega)

/-- **Theorem 1, second proof** (appendix of the paper): the linear part by Lemma 2, the
constant on one flat-folded state obtained by crimping and unfolding. -/
theorem sum_rows_eq_vertex_row_of_flat {x : ι → ι → ZMod 2} (hx : w.Antisymm x) :
    ∑ r ∈ w.rows, r.eval x = ∑ k ∈ w.C, x k (nxt w.C k) + 1 := by
  by_cases h2 : w.C.card = 2
  · exact sum_rows_eq_vertex_row_two hx h2
  have h3 : 3 ≤ w.C.card := by have := w.two_le; omega
  obtain ⟨h, ⟨hinj, hsol⟩, hs⟩ := exists_flat _ w rfl
  have e := sum_rows_add_vertex_eq hx (antisymm_xOf hinj) h3
  rw [Finset.sum_eq_zero (fun r hr => hsol r hr), hs] at e
  generalize ∑ r ∈ w.rows, r.eval x = A at e ⊢
  generalize ∑ k ∈ w.C, x k (nxt w.C k) = B at e ⊢
  revert A B; decide

/-- Every solution of the rows satisfies the vertex row. -/
theorem vertex_row_of_sol {x : ι → ι → ZMod 2} (hx : w.Antisymm x) (hs : w.IsSol x) :
    ∑ k ∈ w.C, x k (nxt w.C k) = 1 := by
  have := sum_rows_eq_vertex_row hx
  rw [Finset.sum_eq_zero (fun r hr => hs r hr)] at this
  generalize ∑ k ∈ w.C, x k (nxt w.C k) = B at this ⊢
  revert B; decide

/-- `M - V = n - 2V` for an assignment of the creases. -/
def mv (w : Walk ι α) (σ : w.C → ZMod 2) : ℤ := (w.C.card : ℤ) - 2 * (w.nV σ : ℤ)

lemma nV_cast (σ : w.C → ZMod 2) : (w.nV σ : ZMod 2) = ∑ k, σ k := by
  unfold nV
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  generalize σ k = u; revert u; decide

lemma card_not_up : 2 * (w.C.filter fun k => ¬ w.up k).card = w.C.card := by
  have := Finset.card_filter_add_card_filter_not (s := w.C) w.up
  rw [card_filter_up] at this; omega

/-- The parity of the number of valleys, through the vertex row. -/
lemma sum_asg (x : ι → ι → ZMod 2) :
    ∑ k, w.asg x k = ∑ k ∈ w.C, x k (nxt w.C k) + ((w.C.filter fun k => ¬ w.up k).card : ZMod 2) := by
  unfold asg
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort w.C (fun k => x k (nxt w.C k)),
    Finset.sum_coe_sort w.C (fun k => if w.up k then (0 : ZMod 2) else 1)]
  congr 1
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- **Maekawa's rule modulo four** holds for every solution of the rows at every vertex:
`M - V ≡ 2 (mod 4)` (Eq. (3) and Corollary 3(a) of the paper, first part). -/
theorem mv_mod_four {x : ι → ι → ZMod 2} (hx : w.Antisymm x) (hs : w.IsSol x) :
    w.mv (w.asg x) % 4 = 2 := by
  have h1 := vertex_row_of_sol hx hs
  have h2 := sum_asg (w := w) x
  rw [h1, ← nV_cast] at h2
  have h3 := card_not_up (w := w)
  set m := (w.C.filter fun k => ¬ w.up k).card
  set V := w.nV (w.asg x)
  have h4 : V % 2 = (1 + m) % 2 := by
    have := (ZMod.natCast_eq_natCast_iff' V (1 + m) 2).1 (by rw [h2]; push_cast; ring)
    exact this
  unfold mv
  rw [← h3]
  push_cast
  omega

end Walk

end Origami
