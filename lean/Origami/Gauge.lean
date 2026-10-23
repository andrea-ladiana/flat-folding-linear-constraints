import Origami.SumRows

/-!
# Theorem 1 by a gauge: cutting the walk at a lowest crease

Number the sectors cyclically starting right after a lowest crease `e_B`: the sector
`nxt B` comes first and the sector `B` last.  Write every layer variable `x_{ab}` with
`a` before `b` in this order.  Then every row at the vertex is homogeneous: a
taco–tortilla row cannot sit at `e_B`, since no sector contains the lowest ray in its
interior, so its two taco sectors are consecutive and the tortilla lies before both or
after both; a taco–taco row has an even number of reversed variables.  The adjacent pairs
are all written forward, `x_{k,k+1}`, except the one at `e_B`, which is written `x_{B+1,B}`.
With Lemma 2, the sum of all the rows is therefore `∑_k x_{k,k+1} + 1 = 0`: the vertex
row.  This is the proof of Theorem 1 in the paper.

Over `𝔽₂` the reordering is the gauge `gauge B a b`, which is `0` when `a` comes before
`b`; the rows are homogeneous in the variables `x + gauge B` (`eval_gauge`), which are
symmetric (`symmOn_add_gauge`).
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-! ### Cyclic order -/

section cyclic

/-- Two distinct points are met in one order or the other, going forward from `k`. -/
lemma cbtw_or_cbtw {k i j : ι} (h : i ≠ j) : cbtw k i j ∨ cbtw k j i := by
  by_cases hi : i = k
  · subst hi; right; exact cbtw_self_right.2 (Ne.symm h)
  by_cases hj : j = k
  · subst hj; left; exact cbtw_self_right.2 h
  exact cbtw_total hi hj h

/-- ... and not in both. -/
lemma cbtw_asymm {k i j : ι} (h : cbtw k i j) : ¬ cbtw k j i := by
  intro h'
  unfold cbtw at h h'
  split_ifs at h h' <;> casesm* _ ∧ _, _ ∨ _ <;> order

/-- decides statements about `cbtw` among a few points, negated hypotheses included -/
syntax "cyc2" : tactic
macro_rules
  | `(tactic| cyc2) => `(tactic| (unfold cbtw at *; split_ifs at * <;>
      (try simp only [not_and_or, not_or, not_lt] at *) <;> casesm* _ ∧ _, _ ∨ _ <;>
      first | order | (left; order) | (right; order) | (constructor <;> order)))

/-- If `B` is not met between `k` and `n`, then from `B` one meets `k` before `n`. -/
lemma cbtw_of_not_cbtw {B k n : ι} (hkB : k ≠ B) (hkn : k ≠ n)
    (h : ¬ cbtw k B n) : cbtw B k n := by
  by_cases hn : n = B
  · subst hn; exact cbtw_self_right.2 hkB
  cyc2

/-- One step forward: if nothing of `{B, g}` lies strictly between `k` and `n`, then from `B`
one meets `k` before `g` exactly when one meets `n` before `g` or `n = g`. -/
lemma cbtw_step {B k n g : ι} (hkB : k ≠ B) (hgk : g ≠ k) (hkn : k ≠ n)
    (h1 : ¬ cbtw k B n) (h2 : ¬ cbtw k g n) : cbtw B k g ↔ (cbtw B n g ∨ n = g) := by
  by_cases hng : n = g
  · subst hng; simp only [or_true, iff_true]; exact cbtw_of_not_cbtw hkB hkn h1
  simp only [hng, or_false]
  by_cases hnB : n = B
  · subst hnB
    simp only [not_cbtw_left, iff_false]
    intro h
    cyc2
  by_cases hgB : g = B
  · subst hgB
    exact ⟨fun _ => cbtw_self_right.2 hng, fun _ => cbtw_self_right.2 hgk.symm⟩
  constructor <;> intro h <;> cyc2

end cyclic

namespace Walk

variable {w : Walk ι α}

/-- From `B`, the crease `k ≠ B` comes before its successor. -/
lemma cbtw_nxt {B k : ι} (hB : B ∈ w.C) (hk : k ∈ w.C) (hkB : k ≠ B) :
    cbtw B k (nxt w.C k) :=
  cbtw_of_not_cbtw hkB (w.nxt_ne hk).symm ((nxt_spec w.nonempty k).2 B hB)

/-- One step forward along the walk, read from `B`. -/
lemma cbtw_nxt_iff {B k g : ι} (hB : B ∈ w.C) (hk : k ∈ w.C) (hg : g ∈ w.C) (hkB : k ≠ B)
    (hgk : g ≠ k) : cbtw B k g ↔ (cbtw B (nxt w.C k) g ∨ nxt w.C k = g) :=
  cbtw_step hkB hgk (w.nxt_ne hk).symm ((nxt_spec w.nonempty k).2 B hB)
    ((nxt_spec w.nonempty k).2 g hg)

/-! ### The gauge -/

variable (w)

/-- The gauge of the cut at `B`: `0` when, read from `B`, the sector `a` comes before the
sector `b` (the sector `nxt B` comes first, the sector `B` last). -/
def gauge (B : ι) (a b : ι) : ZMod 2 := if cbtw B a b then 0 else 1

variable {w}

lemma gauge_swap {B a b : ι} (hab : a ≠ b) : gauge B b a = gauge B a b + 1 := by
  unfold gauge
  rcases cbtw_or_cbtw (k := B) hab with h | h
  · rw [if_neg (cbtw_asymm h), if_pos h]; decide
  · rw [if_pos h, if_neg (cbtw_asymm h)]; decide

/-- The gauge is constant along a crease `k ≠ B`, seen from a third sector `g`. -/
lemma gauge_nxt {B k g : ι} (hB : B ∈ w.C) (hk : k ∈ w.C) (hg : g ∈ w.C) (hkB : k ≠ B)
    (hgk : g ≠ k) (hgn : g ≠ nxt w.C k) : gauge B k g = gauge B (nxt w.C k) g := by
  unfold gauge
  have := cbtw_nxt_iff hB hk hg hkB hgk
  rw [show (nxt w.C k = g) = False from propext ⟨fun e => hgn e.symm, False.elim⟩,
    or_false] at this
  simp only [this]

/-- The gauge on the adjacent pairs: `1` exactly at the cut. -/
lemma gauge_adj {B k : ι} (hB : B ∈ w.C) (hk : k ∈ w.C) :
    gauge B k (nxt w.C k) = if k = B then 1 else 0 := by
  unfold gauge
  by_cases hkB : k = B
  · subst hkB; simp [not_cbtw_left]
  · rw [if_pos (cbtw_nxt hB hk hkB), if_neg hkB]

lemma sum_gauge_adj {B : ι} (hB : B ∈ w.C) : ∑ k ∈ w.C, gauge B k (nxt w.C k) = 1 := by
  rw [Finset.sum_congr rfl fun k hk => gauge_adj hB hk, Finset.sum_ite_eq' w.C B, if_pos hB]

/-- With an antisymmetric `x`, the gauged variables `x + gauge B` are symmetric. -/
lemma symmOn_add_gauge {x : ι → ι → ZMod 2} (hx : w.Antisymm x) (B : ι) :
    w.SymmOn (x + gauge B) := by
  intro i hi j hj hij
  simp only [Pi.add_apply]
  rw [hx i hi j hj hij, gauge_swap hij]
  generalize x i j = u; generalize gauge B i j = v
  revert u v; decide

/-- A crease interior to a sector is not a lowest crease. -/
lemma ne_of_isTT_of_min {B q g : ι} (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) (h : w.IsTT q g) :
    q ≠ B := by
  rintro rfl
  obtain ⟨-, hg, h1, -⟩ := h
  have := hmin _ (lc_mem hg)
  rw [c_lc hg] at this
  exact absurd h1 (not_lt.2 this)

/-- **Every row is homogeneous in the gauge of a lowest crease.**  Taco–taco rows are
homogeneous in the gauge of any crease. -/
theorem eval_gauge {B : ι} (hB : B ∈ w.C) (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) {r : Row ι}
    (hr : r ∈ w.rows) : r.eval (gauge B) = 0 := by
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, hqg, rfl⟩ := mem_ttRows.1 hr
    obtain ⟨h1, h2⟩ := tt_distinct hqg
    rw [Row.eval_tt, gauge_nxt hB hqg.1 hqg.2.1 (ne_of_isTT_of_min hmin hqg) (Ne.symm h1)
      (Ne.symm h2)]
    generalize gauge B (nxt w.C q) g = u; revert u; decide
  · obtain ⟨q, l, -, hql, rfl⟩ := mem_tcRows.1 hr
    obtain ⟨d1, d2, d3, d4⟩ := tc_distinct hql
    have hq := hql.1; have hl := hql.2.1
    rw [Row.eval_tc]
    by_cases hqB : q = B
    · -- pair the terms along the crease `l` instead
      have hlB : l ≠ B := fun e => d1 (hqB.trans e.symm)
      have e1 := gauge_nxt (g := q) hB hl hq hlB d1 d2
      have e2 := gauge_nxt (g := nxt w.C q) hB hl (w.nxt_mem hq) hlB d3 d4
      rw [gauge_swap (Ne.symm d1), gauge_swap (Ne.symm d3), gauge_swap (Ne.symm d2),
        gauge_swap (Ne.symm d4), e1, e2]
      generalize gauge B (nxt w.C l) q = u; generalize gauge B (nxt w.C l) (nxt w.C q) = v
      revert u v; decide
    · have e1 := gauge_nxt (g := l) hB hq hl hqB (Ne.symm d1) (Ne.symm d3)
      have e2 := gauge_nxt (g := nxt w.C l) hB hq (w.nxt_mem hl) hqB (Ne.symm d2) (Ne.symm d4)
      rw [e1, e2]
      generalize gauge B (nxt w.C q) l = u; generalize gauge B (nxt w.C q) (nxt w.C l) = v
      revert u v; decide

/-- **Theorem 1, by the gauge of a lowest crease.**  At every closed walk with at least three
creases, the sum of all the rows is the vertex row, identically in the layer variables. -/
theorem sum_rows_eq_vertex_row_gauge {x : ι → ι → ZMod 2} (hx : w.Antisymm x)
    (h3 : 3 ≤ w.C.card) :
    ∑ r ∈ w.rows, r.eval x = ∑ k ∈ w.C, x k (nxt w.C k) + 1 := by
  obtain ⟨B, hB, hmin⟩ := w.C.exists_min_image w.c w.nonempty
  have hy := symmOn_add_gauge hx B
  have hrow : ∀ r ∈ w.rows, r.eval x = r.eval (x + gauge B) := by
    intro r hr
    rw [Row.eval_add, eval_gauge hB hmin hr, add_zero]
  rw [Finset.sum_congr rfl hrow, sum_rows_symm hy h3]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, sum_gauge_adj hB]

end Walk

end Origami
