import Origami.Theorem1
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-!
# The sign identity (Eq. (8)) and the parity lemma (Lemma 5)

At a generic vertex every pair of sectors `{a, b}` occurs in the sum of the taco–tortilla rows
as many times as there are endpoints of either interval inside the other (Eq. (7)).  Reading
the occurrences with their orientation, the sum of the taco–tortilla rows is, identically in
the antisymmetric layer variables,

  `∑_rows r.eval x = ∑_a x a (nxt a) + S + D`        (Eq. (8), additive form)

where `S` is the number of staggered pairs of non-adjacent sectors and `D` the number of
creases `a` with `|I_{a+1}| < |I_a|`.  The proof here follows the paper: a non-adjacent pair
contributes `1` exactly when it is staggered, an adjacent pair `{a, a+1}` contributes
`x a (a+1)`, plus `1` when the second sector is the shorter.

**Lemma 5** (`S + D` is odd) then follows by comparing with Theorem 1.  The paper proves
Lemma 5 in Appendix A by Whitney's formula, by wall crossings and by a single flat-folded
state; here it is a consequence of Theorem 1, proved by the gauge of a lowest crease.
The parity of an endpoint count is computed through `[min u v < p < max u v] =
[u < p] + [v < p]`, so that the count of a pair plus the count of the reversed pair is four
comparisons of distinct positions, each counted in both directions.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- `[u < v]` over `𝔽₂`. -/
def lt2 (u v : α) : ZMod 2 := if u < v then 1 else 0

lemma lt2_add_lt2 {u v : α} (h : u ≠ v) : lt2 u v + lt2 v u = 1 := by
  unfold lt2
  rcases lt_or_gt_of_ne h with h1 | h1
  · rw [if_pos h1, if_neg (not_lt.2 h1.le)]; rfl
  · rw [if_neg (not_lt.2 h1.le), if_pos h1]; rfl

/-- A point lies strictly between `u` and `v` iff exactly one of them lies below it. -/
lemma between_eq {u v p : α} (hu : p ≠ u) (hv : p ≠ v) :
    (if min u v < p ∧ p < max u v then (1 : ZMod 2) else 0) = lt2 u p + lt2 v p := by
  unfold lt2
  simp only [min_lt_iff, lt_max_iff]
  rcases lt_or_gt_of_ne hu with h1 | h1 <;> rcases lt_or_gt_of_ne hv with h2 | h2 <;>
    simp [h1, h2, not_lt.2 h1.le, not_lt.2 h2.le] <;> decide

/-- Splitting a double sum into the diagonal and the pairs `a < b`. -/
lemma sum_sum_eq_diag_add {M : Type*} [AddCommMonoid M] (s : Finset ι) (f : ι → ι → M) :
    ∑ a ∈ s, ∑ b ∈ s, f a b =
      ∑ a ∈ s, f a a + ∑ a ∈ s, ∑ b ∈ s, if a < b then f a b + f b a else 0 := by
  have h : ∀ a b, f a b = ((if a = b then f a b else 0) + (if a < b then f a b else 0)) +
      (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp
    · simp [h, h.ne', not_lt.2 h.le]
  have h2 : ∑ a ∈ s, ∑ b ∈ s, (if b < a then f a b else 0) =
      ∑ a ∈ s, ∑ b ∈ s, (if a < b then f b a else 0) := Finset.sum_comm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h a b]
  simp only [Finset.sum_add_distrib]
  rw [h2, add_assoc]
  congr 1
  · rw [Finset.sum_congr rfl fun a _ => Finset.sum_ite_eq s a (fun b => f a b)]
    exact Finset.sum_congr rfl fun a ha => if_pos ha
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp

namespace Walk

variable {w : Walk ι α}

variable (w)

/-- The number of endpoints of the interval of `a` in the interior of that of `b`. -/
def nIn (a b : ι) : ℕ :=
  (if w.lo b < w.c (prv w.C a) ∧ w.c (prv w.C a) < w.hi b then 1 else 0) +
    (if w.lo b < w.c a ∧ w.c a < w.hi b then 1 else 0)

/-- Two sectors are staggered: each contains exactly one endpoint of the other. -/
def Staggered (a b : ι) : Prop := w.nIn a b = 1 ∧ w.nIn b a = 1

instance (a b : ι) : Decidable (w.Staggered a b) := by unfold Staggered; infer_instance

/-- `S`: the number of staggered pairs of non-adjacent sectors. -/
def S : ℕ := ((w.C ×ˢ w.C).filter fun p => p.1 < p.2 ∧ ¬ w.Adj p.1 p.2 ∧ w.Staggered p.1 p.2).card

/-- `D`: the number of creases `a` with `|I_{a+1}| < |I_a|`. -/
def D : ℕ := (w.C.filter fun a => w.len (nxt w.C a) < w.len a).card

variable {w}

lemma nIn_le (a b : ι) : w.nIn a b ≤ 2 := by unfold nIn; split_ifs <;> omega

lemma nIn_self (a : ι) : w.nIn a a = 0 := by
  have := not_mem_interior_end (w := w) (g := a)
  unfold nIn; rw [if_neg this.2, if_neg this.1]

/-- The count of a pair with distinct endpoints, as four comparisons. -/
lemma nIn_cast {a b : ι} (h1 : w.c (prv w.C a) ≠ w.c (prv w.C b)) (h2 : w.c (prv w.C a) ≠ w.c b)
    (h3 : w.c a ≠ w.c (prv w.C b)) (h4 : w.c a ≠ w.c b) :
    (w.nIn a b : ZMod 2) = lt2 (w.c (prv w.C b)) (w.c (prv w.C a)) + lt2 (w.c b) (w.c (prv w.C a)) +
      (lt2 (w.c (prv w.C b)) (w.c a) + lt2 (w.c b) (w.c a)) := by
  unfold nIn lo hi
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [between_eq h1 h2, between_eq h3 h4]

/-- For non-adjacent sectors at a generic vertex, the two counts have the same parity:
disjoint `0 + 0`, nested `2 + 0`, staggered `1 + 1`. -/
lemma nIn_add_nIn (hg : w.Generic) {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hab : a ≠ b)
    (hadj : ¬ w.Adj a b) : (w.nIn a b : ZMod 2) + w.nIn b a = 0 := by
  have hpa := w.prv_mem ha; have hpb := w.prv_mem hb
  have d1 : prv w.C a ≠ prv w.C b := fun e => hab (prv_injOn ha hb e)
  have d2 : prv w.C a ≠ b := fun e => hadj (Or.inr (by rw [← e, nxt_prv ha]))
  have d3 : a ≠ prv w.C b := fun e => hadj (Or.inl (by rw [e, nxt_prv hb]))
  have inj : ∀ {i j}, i ∈ w.C → j ∈ w.C → i ≠ j → w.c i ≠ w.c j :=
    fun hi hj hij e => hij (hg hi hj e)
  rw [nIn_cast (inj hpa hpb d1) (inj hpa hb d2) (inj ha hpb d3) (inj ha hb hab),
    nIn_cast (inj hpb hpa (Ne.symm d1)) (inj hpb ha (Ne.symm d3)) (inj hb hpa (Ne.symm d2))
      (inj hb ha (Ne.symm hab))]
  have e1 := lt2_add_lt2 (inj hpa hpb d1)
  have e2 := lt2_add_lt2 (inj hpa hb d2)
  have e3 := lt2_add_lt2 (inj ha hpb d3)
  have e4 := lt2_add_lt2 (inj ha hb hab)
  have e5 : (4 : ZMod 2) = 0 := rfl
  linear_combination e1 + e2 + e3 + e4 + e5

/-- A non-adjacent pair contributes `1` to the sum of the rows exactly when it is staggered. -/
lemma pair_nonadj (hg : w.Generic) {x : ι → ι → ZMod 2} (hx : w.Antisymm x) {a b : ι}
    (ha : a ∈ w.C) (hb : b ∈ w.C) (hab : a ≠ b) (hadj : ¬ w.Adj a b) :
    (w.nIn a b : ZMod 2) * x a b + (w.nIn b a : ZMod 2) * x b a =
      if w.Staggered a b then 1 else 0 := by
  have he := nIn_add_nIn hg ha hb hab hadj
  rw [hx a ha b hb hab]
  have h1 : (w.nIn a b : ZMod 2) * x a b + (w.nIn b a : ZMod 2) * (x a b + 1) =
      (w.nIn b a : ZMod 2) := by linear_combination x a b * he
  rw [h1]
  have hev : Even (w.nIn a b + w.nIn b a) := by
    rw [← ZMod.natCast_eq_zero_iff_even]; push_cast; exact he
  have l1 := nIn_le (w := w) a b
  have l2 := nIn_le (w := w) b a
  obtain ⟨r, hr⟩ := hev
  by_cases hs : w.Staggered a b
  · rw [if_pos hs, hs.2, Nat.cast_one]
  · rw [if_neg hs]
    unfold Staggered at hs
    have : w.nIn b a = 0 ∨ w.nIn b a = 2 := by omega
    rcases this with e | e <;> rw [e] <;> rfl

/-- An adjacent pair `{a, a+1}` contributes `x a (a+1)`, plus `1` if `I_{a+1}` is the shorter. -/
lemma pair_adj (hg : w.Generic) (h3 : 3 ≤ w.C.card) {x : ι → ι → ZMod 2} (hx : w.Antisymm x)
    {a : ι} (ha : a ∈ w.C) :
    (w.nIn a (nxt w.C a) : ZMod 2) * x a (nxt w.C a) +
      (w.nIn (nxt w.C a) a : ZMod 2) * x (nxt w.C a) a =
      x a (nxt w.C a) + if w.len (nxt w.C a) < w.len a then 1 else 0 := by
  have hb := w.nxt_mem ha
  have hpb : prv w.C (nxt w.C a) = a := prv_nxt ha
  have hpa := w.prv_mem ha
  have hne : prv w.C a ≠ nxt w.C a := (nxt_ne_prv ha h3).symm
  have hcne : w.c (prv w.C a) ≠ w.c (nxt w.C a) := fun e => hne (hg hpa hb e)
  have n1 : w.nIn a (nxt w.C a) = if w.len (nxt w.C a) < w.len a then 0 else 1 := by
    unfold nIn len lo hi
    rw [hpb]
    by_cases hu : w.up a
    · have u1 : w.c (prv w.C a) < w.c a := hu
      have u2 : w.c (nxt w.C a) < w.c a := (up_iff_nxt ha).1 hu
      rcases lt_or_gt_of_ne hcne with h | h
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_right, max_eq_left]
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_right, max_eq_left]
    · have u1 : w.c a < w.c (prv w.C a) := (not_up_iff ha).1 hu
      have u2 : w.c a < w.c (nxt w.C a) := (not_up_iff_nxt ha).1 hu
      rcases lt_or_gt_of_ne hcne with h | h
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_left, max_eq_right]
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_left, max_eq_right]
  have n2 : w.nIn (nxt w.C a) a = if w.len (nxt w.C a) < w.len a then 1 else 0 := by
    unfold nIn len lo hi
    rw [hpb]
    by_cases hu : w.up a
    · have u1 : w.c (prv w.C a) < w.c a := hu
      have u2 : w.c (nxt w.C a) < w.c a := (up_iff_nxt ha).1 hu
      rcases lt_or_gt_of_ne hcne with h | h
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_right, max_eq_left]
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_right, max_eq_left]
    · have u1 : w.c a < w.c (prv w.C a) := (not_up_iff ha).1 hu
      have u2 : w.c a < w.c (nxt w.C a) := (not_up_iff_nxt ha).1 hu
      rcases lt_or_gt_of_ne hcne with h | h
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_left, max_eq_right]
      · simp [u1, u2, u1.le, u2.le, h, not_lt.2 h.le, min_eq_left, max_eq_right]
  rw [n1, n2, hx a ha _ hb (w.nxt_ne ha).symm]
  split_ifs <;> push_cast <;> ring

/-- The sum of the taco–tortilla rows, as a sum over ordered pairs of sectors weighted by
Eq. (7). -/
lemma sum_ttRows (x : ι → ι → ZMod 2) :
    ∑ r ∈ w.ttRows, r.eval x = ∑ a ∈ w.C, ∑ b ∈ w.C, (w.nIn a b : ZMod 2) * x a b := by
  unfold ttRows
  rw [Finset.sum_image (fun p _ q _ e => by
    simp only [Row.tt.injEq] at e; exact Prod.ext e.1 e.2.2)]
  rw [Finset.sum_filter, Finset.sum_product]
  simp only [Row.eval_tt]
  have h1 : ∀ q ∈ w.C, ∑ g ∈ w.C, (if w.lo g < w.c q ∧ w.c q < w.hi g then
      x q g + x (nxt w.C q) g else 0) =
      ∑ g ∈ w.C, (if w.lo g < w.c q ∧ w.c q < w.hi g then x q g else 0) +
        ∑ g ∈ w.C, (if w.lo g < w.c q ∧ w.c q < w.hi g then x (nxt w.C q) g else 0) := by
    intro q _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by split_ifs <;> simp
  have h2 : ∑ q ∈ w.C, ∑ g ∈ w.C,
      (if w.lo g < w.c q ∧ w.c q < w.hi g then x (nxt w.C q) g else 0) =
      ∑ a ∈ w.C, ∑ g ∈ w.C,
        (if w.lo g < w.c (prv w.C a) ∧ w.c (prv w.C a) < w.hi g then x a g else 0) :=
    Finset.sum_nbij' (nxt w.C) (prv w.C) (fun a ha => w.nxt_mem ha) (fun a ha => w.prv_mem ha)
      (fun a ha => prv_nxt ha) (fun a ha => nxt_prv ha) (fun a ha => by rw [prv_nxt ha])
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold nIn
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  split_ifs <;> ring

/-- **Eq. (8), additive form.**  At a generic vertex, identically in the antisymmetric layer
variables, the sum of the taco–tortilla rows is `∑_a x_{a,a+1} + S + D`. -/
theorem sum_ttRows_eq (hg : w.Generic) (h3 : 3 ≤ w.C.card) {x : ι → ι → ZMod 2}
    (hx : w.Antisymm x) :
    ∑ r ∈ w.ttRows, r.eval x = ∑ k ∈ w.C, x k (nxt w.C k) + ((w.S + w.D : ℕ) : ZMod 2) := by
  rw [sum_ttRows, sum_sum_eq_diag_add]
  simp only [nIn_self, Nat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
  set Q : ι → ZMod 2 := fun a => x a (nxt w.C a) + if w.len (nxt w.C a) < w.len a then 1 else 0
  -- the contribution of a pair `a < b`
  have hP : ∀ a ∈ w.C, ∀ b ∈ w.C, (if a < b then
      (w.nIn a b : ZMod 2) * x a b + (w.nIn b a : ZMod 2) * x b a else 0) =
      ((if a < b ∧ ¬ w.Adj a b ∧ w.Staggered a b then 1 else 0) +
        (if b = nxt w.C a then (if a < b then Q a else 0) else 0)) +
        (if a = nxt w.C b then (if a < b then Q b else 0) else 0) := by
    intro a ha b hb
    by_cases hab : a < b
    · simp only [hab, if_true, true_and]
      by_cases e1 : b = nxt w.C a
      · have e2 : a ≠ nxt w.C b := fun e => by
          have := card_le_two_of_nxt_nxt ha (by rw [← e1, ← e])
          omega
        subst e1
        rw [pair_adj hg h3 hx ha,
          if_neg (show ¬(¬ w.Adj a (nxt w.C a) ∧ w.Staggered a (nxt w.C a)) from
            fun h => h.1 (Or.inl rfl)), if_pos rfl, if_neg e2]
        simp [Q]
      · by_cases e2 : a = nxt w.C b
        · subst e2
          rw [add_comm, pair_adj hg h3 hx hb,
            if_neg (show ¬(¬ w.Adj (nxt w.C b) b ∧ w.Staggered (nxt w.C b) b) from
              fun h => h.1 (Or.inr rfl)), if_neg e1, if_pos rfl]
          simp [Q]
        · have hadj : ¬ w.Adj a b := fun h => h.elim e1 e2
          rw [pair_nonadj hg hx ha hb hab.ne hadj, if_neg e1, if_neg e2]
          simp [hadj]
    · simp [hab]
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hP a ha b hb]
  simp only [Finset.sum_add_distrib]
  have hB : ∑ a ∈ w.C, ∑ b ∈ w.C, (if b = nxt w.C a then (if a < b then Q a else 0) else 0) =
      ∑ a ∈ w.C, (if a < nxt w.C a then Q a else 0) :=
    Finset.sum_congr rfl fun a ha => by rw [Finset.sum_ite_eq']; exact if_pos (w.nxt_mem ha)
  have hC : ∑ a ∈ w.C, ∑ b ∈ w.C, (if a = nxt w.C b then (if a < b then Q b else 0) else 0) =
      ∑ b ∈ w.C, (if nxt w.C b < b then Q b else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b hb => by rw [Finset.sum_ite_eq']; exact if_pos (w.nxt_mem hb)
  -- the staggered pairs give `S`
  have hS : ∑ a ∈ w.C, ∑ b ∈ w.C, (if a < b ∧ ¬ w.Adj a b ∧ w.Staggered a b then (1 : ZMod 2)
      else 0) = (w.S : ZMod 2) := by
    unfold S
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  -- each adjacent pair once
  have hA : ∑ a ∈ w.C, (if a < nxt w.C a then Q a else 0) +
      ∑ a ∈ w.C, (if nxt w.C a < a then Q a else 0) = ∑ a ∈ w.C, Q a := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rcases lt_or_gt_of_ne (w.nxt_ne ha) with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, not_lt.2 h.le]
  have hD : ∑ a ∈ w.C, Q a = ∑ k ∈ w.C, x k (nxt w.C k) + (w.D : ZMod 2) := by
    simp only [Q, Finset.sum_add_distrib]
    unfold D
    rw [Finset.card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hS, hB, hC, add_assoc, hA, hD]
  push_cast
  ring

/-- **Lemma 5 (parity).**  At every generic vertex, `S + D` is odd. -/
theorem lemma2 (hg : w.Generic) (h3 : 3 ≤ w.C.card) : Odd (w.S + w.D) := by
  set x : ι → ι → ZMod 2 := fun i j => if i < j then 0 else 1
  have hx : w.Antisymm x := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · simp only [x, if_pos h, if_neg (not_lt.2 h.le)]; decide
    · simp only [x, if_pos h, if_neg (not_lt.2 h.le)]; decide
  have h1 := sum_rows_eq_vertex_row hx
  rw [rows, tcRows_eq_empty_of_generic hg, Finset.union_empty, sum_ttRows_eq hg h3 hx] at h1
  rw [← ZMod.natCast_eq_one_iff_odd]
  linear_combination h1

end Walk

end Origami
