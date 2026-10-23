import Origami.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Theorem 4: the linear constraints give the affine hull of the flat-foldable assignments

For every closed walk and every chain of Hull's recursion,

  `W_lin = aff_{𝔽₂} W_flat = W₄`,  `|W_lin| = 2^(n-1-E)`,  `γ = E + 1`.

Proof (Remark 1 of the paper, "a proof without Hull's theorem", organised as a cycle of
inclusions):

* `W₄` is cut out by the parities of the blocks of the recursion (`W4_eq_part`);
* `W₄ ⊆ aff W_flat`: one flat-folded state lies in `W₄` (`exists_base`), and the differences
  of flat-foldable assignments contain `e_i + e_j` for any two creases of one block: single
  crimps give consecutive creases, lifting along a run carries them up (`InDir`);
* `aff W_flat ⊆ W_lin`, since `W_lin` is affine;
* `W_lin ⊆ Comp`: every solution satisfies the equation of every component (Lemma 3);
* `Comp ⊆ W₄`: the components refine the blocks (Lemma 4, `lab_eq_of_sameComp`).
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-! ### Assignments as functions on all creases -/

/-- An assignment of the creases, extended by zero. -/
def ext0 (w : Walk ι α) (σ : w.C → ZMod 2) : ι → ZMod 2 :=
  fun j => if h : j ∈ w.C then σ ⟨j, h⟩ else 0

lemma ext0_mem (σ : w.C → ZMod 2) (j : w.C) : w.ext0 σ j.1 = σ j := by
  simp [ext0, j.2]

lemma ext0_add (σ τ : w.C → ZMod 2) : w.ext0 (σ + τ) = w.ext0 σ + w.ext0 τ := by
  funext j; simp only [ext0, Pi.add_apply]; by_cases h : j ∈ w.C <;> simp [h]

/-- Sums over a set of creases of an assignment. -/
lemma sum_subtype_filter (σ : w.C → ZMod 2) (P : ι → Prop) [DecidablePred P] :
    ∑ j ∈ (Finset.univ.filter fun j : w.C => P j.1), σ j = ∑ j ∈ w.C.filter P, w.ext0 σ j := by
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_coe_sort w.C (fun j => if P j then w.ext0 σ j else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ext0_mem]

/-- Two assignments agree iff their extensions do. -/
lemma ext0_inj {σ τ : w.C → ZMod 2} (h : ∀ j ∈ w.C, w.ext0 σ j = w.ext0 τ j) : σ = τ := by
  funext j; rw [← ext0_mem σ j, ← ext0_mem τ j]; exact h j.1 j.2

/-! ### `M - V` modulo four as a parity -/

lemma card_filter_one (σ : w.C → ZMod 2) (S : Finset ι) :
    ((Finset.univ.filter fun j : w.C => j.1 ∈ S ∧ σ j = 1).card : ZMod 2) =
      ∑ j ∈ w.C.filter (· ∈ S), w.ext0 σ j := by
  rw [← sum_subtype_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.1 ∈ S
  · simp only [hj, true_and, if_true]
    generalize σ j = u; revert u; decide
  · simp [hj]

/-- For an even number `2p` of creases, `M - V ≡ 0 (mod 4)` iff `V ≡ p (mod 2)`. -/
lemma mvOn_even_iff (σ : w.C → ZMod 2) {S : Finset ι} (hS : S ⊆ w.C) {p : ℕ}
    (hp : S.card = 2 * p) :
    Chain.mvOn σ S % 4 = 0 ↔ ∑ j ∈ w.C.filter (· ∈ S), w.ext0 σ j = (p : ZMod 2) := by
  unfold Chain.mvOn
  rw [← card_filter_one, hp]
  set V := (Finset.univ.filter fun j : w.C => j.1 ∈ S ∧ σ j = 1).card
  rw [ZMod.natCast_eq_natCast_iff']
  push_cast
  omega

/-- For an odd number `2p + 1` of creases, the value of `σ_⋆` is the parity of `V + p`. -/
lemma starVal_eq (R : w.RunData) (hk : ¬ Even R.k) (σ : w.C → ZMod 2) :
    Chain.starVal R σ =
      ∑ j ∈ w.C.filter (· ∈ insert R.A R.B), w.ext0 σ j + ((R.k + 1) / 2 : ℕ) := by
  have hAB : R.A ∉ R.B := by have := R.star_not_mem_B; rwa [R.star_odd hk] at this
  have hcard : (insert R.A R.B).card = R.k + 2 := by
    rw [Finset.card_insert_of_notMem hAB, R.card_B, if_neg hk]
  obtain ⟨p, hp⟩ : ∃ p, R.k = 2 * p + 1 := ⟨R.k / 2, by
    rcases Nat.even_or_odd R.k with h | ⟨q, hq⟩ <;> [exact absurd h hk; omega]⟩
  unfold Chain.starVal Chain.mvOn
  rw [← card_filter_one, hcard]
  set V := (Finset.univ.filter fun j : w.C => j.1 ∈ insert R.A R.B ∧ σ j = 1).card
  have h2 : (R.k + 1) / 2 = p + 1 := by omega
  rw [h2]
  rw [← Nat.cast_add, ← ZMod.natCast_mod (V + (p + 1)) 2]
  split_ifs with h
  · -- `k + 2 - 2V ≡ 1`, so `V ≡ p + 1`
    have : (V + (p + 1)) % 2 = 0 := by push_cast at h; omega
    rw [this]; rfl
  · have : (V + (p + 1)) % 2 = 1 := by push_cast at h; omega
    rw [this]; rfl

/-- For an even number `2p` of creases, `M - V ≡ 2 (mod 4)` iff `V ≡ p + 1 (mod 2)`. -/
lemma mvOn_two_iff (σ : w.C → ZMod 2) {S : Finset ι} {p : ℕ} (hp : S.card = 2 * p) :
    Chain.mvOn σ S % 4 = 2 ↔ ∑ j ∈ w.C.filter (· ∈ S), w.ext0 σ j = ((p + 1 : ℕ) : ZMod 2) := by
  unfold Chain.mvOn
  rw [← card_filter_one, hp]
  set V := (Finset.univ.filter fun j : w.C => j.1 ∈ S ∧ σ j = 1).card
  rw [ZMod.natCast_eq_natCast_iff']
  push_cast
  omega

lemma mv_eq_mvOn (σ : w.C → ZMod 2) : w.mv σ = Chain.mvOn σ w.C := by
  unfold mv Chain.mvOn nV
  rw [show (Finset.univ.filter fun j : w.C => j.1 ∈ w.C ∧ σ j = 1) =
    Finset.univ.filter (fun j => σ j = 1) from by ext j; simp [j.2]]

/-! ### Spaces cut out by sums over classes -/

/-- The sum of an assignment over the creases related to `j₀`. -/
noncomputable def bsum (w : Walk ι α) (r : ι → ι → Prop) (σ : w.C → ZMod 2) (j₀ : ι) : ZMod 2 :=
  ∑ j ∈ w.C.filter (r j₀), w.ext0 σ j

/-- The assignments with the same sum as `σ₀` over every class of `r`. -/
def Part (w : Walk ι α) (r : ι → ι → Prop) (σ₀ : w.C → ZMod 2) : Set (w.C → ZMod 2) :=
  {σ | ∀ j₀ ∈ w.C, w.bsum r σ j₀ = w.bsum r σ₀ j₀}

/-- Two creases in the same block of the recursion. -/
def labRel (c : Chain w) : ι → ι → Prop := fun a b => c.lab a = c.lab b

lemma sum_union_disj {s t : Finset ι} (h : Disjoint s t) (f : ι → ZMod 2) :
    ∑ j ∈ s ∪ t, f j = ∑ j ∈ s, f j + ∑ j ∈ t, f j := Finset.sum_union h

/-- The extension of the induced assignment of the crimped walk. -/
lemma ext0_restrict (R : w.RunData) (σ : w.C → ZMod 2) (j : ι) :
    (w.runCrimp R).ext0 (Chain.restrict R σ) j =
      if j ∈ (w.runCrimp R).C then (if Even R.k ∨ j ≠ R.A then w.ext0 σ j else Chain.starVal R σ)
      else 0 := by
  unfold ext0 Chain.restrict
  by_cases hj : j ∈ (w.runCrimp R).C
  · have hjC : j ∈ w.C := (Finset.mem_sdiff.1 hj).1
    simp only [hj, hjC, dif_pos, if_true]
  · simp only [hj, dif_neg, not_false_eq_true, if_false]

lemma A_not_C' (R : w.RunData) (hk : Even R.k) : R.A ∉ (w.runCrimp R).C := fun h =>
  (Finset.mem_sdiff.1 h).2 (R.t_mem_B (i := 0) (by simp [hk]) (by omega))

lemma A_mem_C' (R : w.RunData) (hk : ¬ Even R.k) : R.A ∈ (w.runCrimp R).C := by
  have := R.star_mem'; rwa [R.star_odd hk] at this

lemma starVal_eq' (R : w.RunData) (hk : ¬ Even R.k) (τ : w.C → ZMod 2) :
    Chain.starVal R τ = w.ext0 τ R.A + ∑ j ∈ R.B, w.ext0 τ j + (((R.k + 1) / 2 : ℕ) : ZMod 2) := by
  have hAB : R.A ∉ R.B := (Finset.mem_sdiff.1 (A_mem_C' R hk)).2
  rw [starVal_eq R hk τ, show w.C.filter (· ∈ insert R.A R.B) = insert R.A R.B from by
    ext j; simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · exact fun h => h.2
    · rintro (rfl | h)
      · exact ⟨R.hA, Or.inl rfl⟩
      · exact ⟨R.B_subset h, Or.inr h⟩, Finset.sum_insert hAB]

/-- Crimping a run does not change the type of a surviving crease. -/
lemma runCrimp_up (R : w.RunData) {q : ι} (hq : q ∈ (w.runCrimp R).C) :
    (w.runCrimp R).up q ↔ w.up q := by
  by_cases hup : w.up R.A
  · exact RunData.up' hup hq
  · have hup' : w.refl.up R.refl'.A := (refl_up R.hA).2 hup
    have e := RunData.up' (R := R.refl') hup' (q := q) hq
    rw [← refl_runCrimp, refl_up hq, refl_up (Finset.mem_sdiff.1 hq).1] at e
    tauto

/-- The blocks after a crimp with `k` even: the run's creases, and the old blocks. -/
lemma filter_lab_even (R : w.RunData) (c : Chain (w.runCrimp R)) (hk : Even R.k) {j₀ : ι}
    (hj₀ : j₀ ∈ w.C) :
    w.C.filter (labRel (Chain.step R c) j₀) =
      if j₀ ∈ R.B then R.B else (w.runCrimp R).C.filter (labRel c j₀) := by
  have hA := A_not_C' R hk
  ext j
  by_cases h0 : j₀ ∈ R.B <;> by_cases h1 : j ∈ R.B
  · simp [labRel, Chain.lab, hk, h0, h1, R.B_subset h1]
  · simp only [Finset.mem_filter, labRel, Chain.lab, hk, h0, h1, if_true, if_false, iff_false]
    rintro ⟨hj, h⟩
    exact hA (h ▸ c.lab_mem (R.mem_C'.2 ⟨hj, h1⟩))
  · have hlab : c.lab j₀ ≠ R.A := fun h => hA (h ▸ c.lab_mem (R.mem_C'.2 ⟨hj₀, h0⟩))
    simp [labRel, Chain.lab, hk, h0, h1, hlab, runCrimp_C, Finset.mem_sdiff]
  · simp only [Finset.mem_filter, labRel, Chain.lab, hk, h0, h1, if_false, runCrimp_C,
      Finset.mem_sdiff, not_false_eq_true, and_true]

/-- The blocks after a crimp with `k` odd: the run's creases join the block of `A`. -/
lemma filter_lab_odd (R : w.RunData) (c : Chain (w.runCrimp R)) (hk : ¬ Even R.k) {j₀ : ι}
    (hj₀ : j₀ ∈ (w.runCrimp R).C) :
    w.C.filter (labRel (Chain.step R c) j₀) =
      if c.lab R.A = c.lab j₀ then (w.runCrimp R).C.filter (labRel c j₀) ∪ R.B
      else (w.runCrimp R).C.filter (labRel c j₀) := by
  have hj₀B : j₀ ∉ R.B := (Finset.mem_sdiff.1 hj₀).2
  ext j
  by_cases h1 : j ∈ R.B
  · have hjC := R.B_subset h1
    have hjC' : j ∉ (w.runCrimp R).C := fun h => (Finset.mem_sdiff.1 h).2 h1
    simp only [Finset.mem_filter, labRel, Chain.lab, hk, hj₀B, h1, if_true, if_false]
    split_ifs with h2
    · simp [h1, hjC, h2.symm]
    · simp only [Finset.mem_filter, hjC', false_and, iff_false, not_and]
      exact fun _ h => h2 h.symm
  · simp only [Finset.mem_filter, labRel, Chain.lab, hk, hj₀B, h1, if_false]
    split_ifs with h2
    · simp [runCrimp_C, Finset.mem_sdiff, h1, labRel]
    · simp [runCrimp_C, Finset.mem_sdiff, h1, labRel]

/-- **`W₄` is cut out by the parities of the blocks of the recursion.** -/
theorem W4_eq_part : ∀ {w : Walk ι α} (c : Chain w) {σ₀ : w.C → ZMod 2}, σ₀ ∈ c.W4 →
    c.W4 = w.Part (labRel c) σ₀ := by
  intro w c
  induction c with
  | @base w h =>
    intro σ₀ h₀
    obtain ⟨m, hm⟩ := card_even (w := w)
    have hm' : w.C.card = 2 * m := by omega
    have key : ∀ σ : w.C → ZMod 2, σ ∈ (Chain.base h).W4 ↔
        ∑ j ∈ w.C.filter (· ∈ w.C), w.ext0 σ j = ((m + 1 : ℕ) : ZMod 2) := by
      intro σ
      show w.mv σ % 4 = 2 ↔ _
      rw [mv_eq_mvOn]; exact mvOn_two_iff σ hm'
    have hall : ∀ j₀, w.C.filter (labRel (Chain.base h) j₀) = w.C.filter (· ∈ w.C) := by
      intro j₀; ext j; simp [labRel, Chain.lab]
    ext σ
    simp only [Part, bsum, Set.mem_setOf_eq, hall]
    rw [key σ]
    have e₀ := (key σ₀).1 h₀
    constructor
    · intro hσ j₀ _; rw [hσ, e₀]
    · intro hσ
      obtain ⟨j₀, hj₀⟩ := w.nonempty
      rw [hσ j₀ hj₀, e₀]
  | @step w R c ih =>
    intro σ₀ h₀
    obtain ⟨h₀1, h₀2⟩ := h₀
    have IH := ih h₀2
    have hBsub := R.B_subset
    have hsub : (w.runCrimp R).C ⊆ w.C := Finset.sdiff_subset
    ext σ
    show ((Even R.k → Chain.mvOn σ R.B % 4 = 0) ∧ Chain.restrict R σ ∈ c.W4) ↔ _
    rw [IH]
    simp only [Part, Set.mem_setOf_eq]
    by_cases hk : Even R.k
    · -- the run's creases form a new block
      obtain ⟨p, hp⟩ : ∃ p, R.B.card = 2 * p := ⟨R.k / 2 + 1, by
        rw [R.card_B, if_pos hk]; obtain ⟨q, hq⟩ := hk; omega⟩
      have hfB : w.C.filter (· ∈ R.B) = R.B := by
        ext j; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hBsub h, h⟩⟩
      have hmv : ∀ τ : w.C → ZMod 2, Chain.mvOn τ R.B % 4 = 0 ↔
          ∑ j ∈ R.B, w.ext0 τ j = (p : ZMod 2) := by
        intro τ; rw [mvOn_even_iff τ hBsub hp, hfB]
      have hbB : ∀ τ : w.C → ZMod 2, ∀ j₀ ∈ R.B,
          w.bsum (labRel (Chain.step R c)) τ j₀ = ∑ j ∈ R.B, w.ext0 τ j := by
        intro τ j₀ hj₀
        unfold bsum; rw [filter_lab_even R c hk (hBsub hj₀), if_pos hj₀]
      have hbs : ∀ τ : w.C → ZMod 2, ∀ j₀ ∈ (w.runCrimp R).C,
          (w.runCrimp R).bsum (labRel c) (Chain.restrict R τ) j₀ =
            w.bsum (labRel (Chain.step R c)) τ j₀ := by
        intro τ j₀ hj₀
        unfold bsum
        rw [filter_lab_even R c hk (hsub hj₀), if_neg (Finset.mem_sdiff.1 hj₀).2]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [ext0_restrict, if_pos (Finset.mem_of_mem_filter j hj), if_pos (Or.inl hk)]
      have e₀ := (hmv σ₀).1 (h₀1 hk)
      constructor
      · rintro ⟨h1, h2⟩ j₀ hj₀
        by_cases hjB : j₀ ∈ R.B
        · rw [hbB σ j₀ hjB, hbB σ₀ j₀ hjB, (hmv σ).1 (h1 hk), e₀]
        · have hj₀' : j₀ ∈ (w.runCrimp R).C := R.mem_C'.2 ⟨hj₀, hjB⟩
          rw [← hbs σ j₀ hj₀', ← hbs σ₀ j₀ hj₀']; exact h2 j₀ hj₀'
      · intro h
        refine ⟨fun _ => ?_, fun j₀ hj₀ => ?_⟩
        · have hAB : R.A ∈ R.B := R.t_mem_B (i := 0) (by simp [hk]) (by omega)
          rw [hmv, ← hbB σ R.A hAB, h R.A R.hA, hbB σ₀ R.A hAB, e₀]
        · rw [hbs σ j₀ hj₀, hbs σ₀ j₀ hj₀]; exact h j₀ (hsub hj₀)
    · -- the run's creases join the block of `A`
      have hA' := A_mem_C' R hk
      have hAB : R.A ∉ R.B := (Finset.mem_sdiff.1 hA').2
      set K : ZMod 2 := (((R.k + 1) / 2 : ℕ) : ZMod 2)
      have hstar : ∀ τ : w.C → ZMod 2,
          Chain.starVal R τ = w.ext0 τ R.A + ∑ j ∈ R.B, w.ext0 τ j + K := starVal_eq' R hk
      have hbs : ∀ τ : w.C → ZMod 2, ∀ j₀ ∈ (w.runCrimp R).C,
          (w.runCrimp R).bsum (labRel c) (Chain.restrict R τ) j₀ =
            w.bsum (labRel (Chain.step R c)) τ j₀ + if c.lab R.A = c.lab j₀ then K else 0 := by
        intro τ j₀ hj₀
        unfold bsum
        set S' := (w.runCrimp R).C.filter (labRel c j₀)
        have hfun : ∀ j ∈ S', (w.runCrimp R).ext0 (Chain.restrict R τ) j =
            w.ext0 τ j + if j = R.A then ∑ j ∈ R.B, w.ext0 τ j + K else 0 := by
          intro j hj
          rw [ext0_restrict, if_pos (Finset.mem_of_mem_filter j hj)]
          by_cases hjA : j = R.A
          · rw [if_neg (by tauto), if_pos hjA, hstar, hjA]; ring
          · rw [if_pos (Or.inr hjA), if_neg hjA, add_zero]
        rw [Finset.sum_congr rfl hfun, Finset.sum_add_distrib, Finset.sum_ite_eq',
          filter_lab_odd R c hk hj₀]
        have hmemA : R.A ∈ S' ↔ c.lab R.A = c.lab j₀ := by
          simp only [S', Finset.mem_filter, labRel, hA', true_and]; exact eq_comm
        by_cases hc : c.lab R.A = c.lab j₀
        · rw [if_pos (hmemA.2 hc), if_pos hc, if_pos hc, sum_union_disj (by
            rw [Finset.disjoint_left]; intro j hj hjB
            exact (Finset.mem_sdiff.1 (Finset.mem_of_mem_filter j hj)).2 hjB)]
          ring
        · rw [if_neg (fun h => hc (hmemA.1 h)), if_neg hc, if_neg hc]
      have hbB : ∀ τ : w.C → ZMod 2, ∀ j₀ ∈ R.B,
          w.bsum (labRel (Chain.step R c)) τ j₀ = w.bsum (labRel (Chain.step R c)) τ R.A := by
        intro τ j₀ hj₀
        unfold bsum labRel
        simp only [Chain.lab, if_pos hj₀, if_neg hk, if_neg hAB]
      constructor
      · rintro ⟨-, h2⟩ j₀ hj₀
        by_cases hjB : j₀ ∈ R.B
        · rw [hbB σ j₀ hjB, hbB σ₀ j₀ hjB]
          have := h2 R.A hA'
          rw [hbs σ R.A hA', hbs σ₀ R.A hA'] at this
          simpa using this
        · have hj₀' : j₀ ∈ (w.runCrimp R).C := R.mem_C'.2 ⟨hj₀, hjB⟩
          have := h2 j₀ hj₀'
          rw [hbs σ j₀ hj₀', hbs σ₀ j₀ hj₀'] at this
          simpa using this
      · intro h
        refine ⟨fun h' => absurd h' hk, fun j₀ hj₀ => ?_⟩
        rw [hbs σ j₀ hj₀, hbs σ₀ j₀ hj₀, h j₀ (hsub hj₀)]

/-! ### Affine spans over `𝔽₂` -/

lemma zmod2_neg (x : ZMod 2) : -x = x := by generalize x = u; revert u; decide

lemma fun_neg {X : Type*} (f : X → ZMod 2) : -f = f := by funext j; exact zmod2_neg _

/-- The affine span of the flat-foldable assignments. -/
abbrev affW (w : Walk ι α) : Set (w.C → ZMod 2) := (affineSpan (ZMod 2) w.Wflat : Set _)

lemma aff_add3 {S : Set (w.C → ZMod 2)} {p q r : w.C → ZMod 2}
    (hp : p ∈ (affineSpan (ZMod 2) S : Set _)) (hq : q ∈ (affineSpan (ZMod 2) S : Set _))
    (hr : r ∈ (affineSpan (ZMod 2) S : Set _)) : p + q + r ∈ (affineSpan (ZMod 2) S : Set _) := by
  have := AffineSubspace.vadd_mem_of_mem_direction
    (AffineSubspace.vsub_mem_direction hp hq) hr
  simpa [vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, fun_neg] using this

/-- A set closed under `p + q + r` contains the affine span of its subsets. -/
lemma affineSpan_subset {S T : Set (w.C → ZMod 2)} (hT : IsAff T) (hST : S ⊆ T) :
    (affineSpan (ZMod 2) S : Set _) ⊆ T := by
  let A : AffineSubspace (ZMod 2) (w.C → ZMod 2) :=
    { carrier := T
      smul_vsub_vadd_mem := by
        intro c p1 p2 p3 h1 h2 h3
        fin_cases c
        · simpa using h3
        · simpa [vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, fun_neg] using hT _ h1 _ h2 _ h3 }
  exact (affineSpan_le (s := S) (Q := A)).2 hST

lemma affW_subset_Wlin : w.affW ⊆ w.Wlin :=
  affineSpan_subset isAff_Wlin Wflat_subset_Wlin

/-! ### A flat-foldable assignment in `W₄` -/

lemma asg_xOf (h : ι → ℤ) (j : w.C) :
    w.asg (xOf h) j = xOf h j.1 (nxt w.C j.1) + if w.up j.1 then 0 else 1 := rfl

/-- Along a run, consecutive creases alternate between maxima and minima, so an even number
of consecutive creases contains as many minima as maxima. -/
lemma sum_minima (R : w.RunData) (i₀ q : ℕ) :
    ∑ i ∈ Finset.Ico i₀ (i₀ + 2 * q), (if w.up (R.t i) then (0 : ZMod 2) else 1) = (q : ZMod 2) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show i₀ + 2 * (q + 1) = (i₀ + 2 * q + 1) + 1 by ring, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega), ih]
    have e : w.up (R.t (i₀ + 2 * q + 1)) ↔ ¬ w.up (R.t (i₀ + 2 * q)) := by
      rw [R.t_succ]; exact up_nxt (R.t_mem _)
    by_cases hu : w.up (R.t (i₀ + 2 * q))
    · rw [if_pos hu, if_neg (fun h => e.1 h hu)]; push_cast; ring
    · rw [if_neg hu, if_pos (e.2 hu)]; push_cast; ring

lemma sum_B_minima (R : w.RunData) :
    ∑ j ∈ R.B, (if w.up j then (0 : ZMod 2) else 1) =
      ((if Even R.k then R.k / 2 + 1 else (R.k + 1) / 2 : ℕ) : ZMod 2) := by
  unfold RunData.B
  split_ifs with hk
  · obtain ⟨m, hm⟩ := hk
    rw [Finset.sum_image (fun i hi j hj e => R.t_inj (by
      have := R.card_even_ge ⟨m, hm⟩; simp at hi; omega) (by
      have := R.card_even_ge ⟨m, hm⟩; simp at hj; omega) e)]
    rw [show Finset.range (R.k + 2) = Finset.Ico 0 (0 + 2 * (R.k / 2 + 1)) by
      rw [Finset.range_eq_Ico]; congr 1; omega]
    exact sum_minima R 0 _
  · rw [Finset.sum_image (fun i hi j hj e => R.t_inj (by
      have := R.hcard; simp at hi; omega) (by have := R.hcard; simp at hj; omega) e)]
    rw [show Finset.Ico 1 (R.k + 2) = Finset.Ico 1 (1 + 2 * ((R.k + 1) / 2)) by
      congr 1; rcases Nat.even_or_odd R.k with h | ⟨q, hq⟩ <;> [exact absurd h hk; omega]]
    exact sum_minima R 1 _

/-- The induced assignment of a state lifted along a run is the old one. -/
lemma restrict_lift (R : w.RunData) {h h' : ι → ℤ}
    (ha : ∀ j ∈ (w.runCrimp R).C, xOf h j (nxt w.C j) = xOf h' j (nxt (w.runCrimp R).C j))
    (hb : ∀ j ∈ R.B, xOf h j (nxt w.C j) = 0) :
    Chain.restrict R (w.asg (xOf h)) = (w.runCrimp R).asg (xOf h') ∧
      (Even R.k → Chain.mvOn (w.asg (xOf h)) R.B % 4 = 0) := by
  have hsumB : ∑ j ∈ R.B, w.ext0 (w.asg (xOf h)) j =
      ((if Even R.k then R.k / 2 + 1 else (R.k + 1) / 2 : ℕ) : ZMod 2) := by
    rw [← sum_B_minima R]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjC := R.B_subset hj
    rw [show w.ext0 (w.asg (xOf h)) j = w.asg (xOf h) ⟨j, hjC⟩ from ext0_mem _ ⟨j, hjC⟩,
      asg_xOf, hb j hj, zero_add]
  have hsame : ∀ j : (w.runCrimp R).C,
      w.asg (xOf h) ⟨j.1, (Finset.mem_sdiff.1 j.2).1⟩ = (w.runCrimp R).asg (xOf h') j := by
    intro j
    rw [asg_xOf, asg_xOf, ha j.1 j.2]
    simp only [runCrimp_up R j.2]
  refine ⟨funext fun j => ?_, fun hk => ?_⟩
  · unfold Chain.restrict
    split_ifs with hj
    · exact hsame j
    · push_neg at hj
      obtain ⟨hk, hjA⟩ := hj
      rw [starVal_eq' R hk, hsumB, if_neg hk, ← hsame j]
      have : w.ext0 (w.asg (xOf h)) R.A = w.asg (xOf h) ⟨j.1, (Finset.mem_sdiff.1 j.2).1⟩ := by
        simp only [ext0, dif_pos R.hA]; congr 1; exact Subtype.ext hjA.symm
      rw [this]
      generalize w.asg (xOf h) ⟨j.1, (Finset.mem_sdiff.1 j.2).1⟩ = u
      generalize (((R.k + 1) / 2 : ℕ) : ZMod 2) = v
      revert u v; decide
  · obtain ⟨p, hp⟩ : ∃ p, R.B.card = 2 * p := ⟨R.k / 2 + 1, by
      rw [R.card_B, if_pos hk]; obtain ⟨q, hq⟩ := hk; omega⟩
    rw [mvOn_even_iff _ R.B_subset hp, show w.C.filter (· ∈ R.B) = R.B from by
      ext j; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨R.B_subset h, h⟩⟩,
      hsumB, if_pos hk]
    congr 1
    rw [R.card_B, if_pos hk] at hp; obtain ⟨q, hq⟩ := hk; omega

/-- **A flat-foldable assignment in `W₄`.** -/
theorem exists_base : ∀ {w : Walk ι α} (c : Chain w), ∃ σ ∈ w.Wflat, σ ∈ c.W4 := by
  intro w c
  induction c with
  | @base w h =>
    obtain ⟨h, hf, -⟩ := exists_flat _ w rfl
    exact ⟨_, ⟨h, hf, rfl⟩, mv_mod_four (antisymm_xOf hf.1) hf.2⟩
  | @step w R c ih =>
    obtain ⟨σ', ⟨h', hf', rfl⟩, hσ'⟩ := ih
    obtain ⟨h, hf, ha, hb⟩ := RunData.runLift _ w R rfl hf'
    obtain ⟨e1, e2⟩ := restrict_lift R ha hb
    exact ⟨_, ⟨h, hf, rfl⟩, e2, by rw [e1]; exact hσ'⟩

/-! ### Directions of `aff W_flat` -/

/-- `δ` is a direction of the affine span of the flat-foldable assignments. -/
def InDir (w : Walk ι α) (δ : w.C → ZMod 2) : Prop := ∀ σ ∈ w.affW, σ + δ ∈ w.affW

lemma inDir_zero : w.InDir 0 := fun σ h => by simpa using h

lemma inDir_add {δ δ' : w.C → ZMod 2} (h : w.InDir δ) (h' : w.InDir δ') : w.InDir (δ + δ') :=
  fun σ hσ => by rw [← add_assoc]; exact h' _ (h σ hσ)

lemma inDir_of_mem {p q : w.C → ZMod 2} (hp : p ∈ w.affW) (hq : q ∈ w.affW) :
    w.InDir (p + q) := fun σ hσ => by
  have := aff_add3 hσ hp hq; rwa [add_assoc] at this

lemma Wflat_subset_affW : w.Wflat ⊆ w.affW := subset_affineSpan (ZMod 2) _

/-- The indicator of one crease. -/
def eC (w : Walk ι α) (j : ι) : w.C → ZMod 2 := fun k => if k.1 = j then 1 else 0

lemma eC_add_self (j : ι) : w.eC j + w.eC j = 0 := by
  funext k; simp only [Pi.add_apply, Pi.zero_apply]; exact (zmod2_add_self _)

lemma inDir_trans {i j k : ι} (h1 : w.InDir (w.eC i + w.eC j)) (h2 : w.InDir (w.eC j + w.eC k)) :
    w.InDir (w.eC i + w.eC k) := by
  have := inDir_add h1 h2
  rwa [show w.eC i + w.eC j + (w.eC j + w.eC k) = w.eC i + w.eC k by
    rw [add_assoc, ← add_assoc (w.eC j), eC_add_self, zero_add]] at this

lemma inDir_symm {i j : ι} (h : w.InDir (w.eC i + w.eC j)) : w.InDir (w.eC j + w.eC i) := by
  rwa [add_comm]

lemma inDir_refl (i : ι) : w.InDir (w.eC i + w.eC i) := by rw [eC_add_self]; exact inDir_zero

/-- **(G1)** A legal single crimp: the two lifts of one state differ exactly on the two deleted
creases. -/
lemma inDir_crimp {a : ι} (hc : w.CrimpOK a) : w.InDir (w.eC (prv w.C a) + w.eC a) := by
  obtain ⟨h', hf', -⟩ := exists_flat _ (w.crimp a hc) rfl
  obtain ⟨hT, hfT, haT, hT1, hT2⟩ := hc.exists_lift hf' true
  obtain ⟨hF, hfF, haF, hF1, hF2⟩ := hc.exists_lift hf' false
  have key : w.asg (xOf hT) + w.asg (xOf hF) = w.eC (prv w.C a) + w.eC a := by
    funext j
    simp only [Pi.add_apply, asg_xOf, eC]
    by_cases h1 : j.1 = prv w.C a
    · rw [h1, if_pos rfl, if_neg hc.A_ne_a, nxt_prv hc.mem, hT1, hF1]
      simp only [if_true, if_false]
      generalize (if w.up (prv w.C a) then (0 : ZMod 2) else 1) = u; revert u; decide
    · by_cases h2 : j.1 = a
      · rw [h2, if_neg hc.A_ne_a.symm, if_pos rfl, hT2, hF2]
        simp only [if_true, if_false]
        generalize (if w.up a then (0 : ZMod 2) else 1) = u; revert u; decide
      · have hj : j.1 ∈ (w.crimp a hc).C := mem_crimpC.2 ⟨h2, h1, j.2⟩
        rw [haT j.1 hj, haF j.1 hj, if_neg h1, if_neg h2]
        generalize xOf h' j.1 (nxt (w.crimp a hc).C j.1) = u
        generalize (if w.up j.1 then (0 : ZMod 2) else 1) = v
        revert u v; decide
  rw [← key]
  exact inDir_of_mem (Wflat_subset_affW ⟨hT, hfT, rfl⟩) (Wflat_subset_affW ⟨hF, hfF, rfl⟩)

/-- The lift of assignments along a run: the old values on the surviving creases, the folded
accordion on the run's creases. -/
def liftAsg (R : w.RunData) (σ' : (w.runCrimp R).C → ZMod 2) : w.C → ZMod 2 :=
  fun j => (w.runCrimp R).ext0 σ' j.1 +
    if j.1 ∈ (w.runCrimp R).C then 0 else (if w.up j.1 then 0 else 1)

lemma liftAsg_add3 (R : w.RunData) (p q r : (w.runCrimp R).C → ZMod 2) :
    liftAsg R (p + q + r) = liftAsg R p + liftAsg R q + liftAsg R r := by
  funext j
  simp only [liftAsg, ext0_add, Pi.add_apply]
  generalize (w.runCrimp R).ext0 p j.1 = a; generalize (w.runCrimp R).ext0 q j.1 = b
  generalize (w.runCrimp R).ext0 r j.1 = c
  generalize (if j.1 ∈ (w.runCrimp R).C then (0 : ZMod 2) else if w.up j.1 then 0 else 1) = d
  revert a b c d; decide

lemma liftAsg_add (R : w.RunData) (p δ : (w.runCrimp R).C → ZMod 2) :
    liftAsg R (p + δ) = liftAsg R p + fun j => (w.runCrimp R).ext0 δ j.1 := by
  funext j
  simp only [liftAsg, ext0_add, Pi.add_apply]
  ring

lemma liftAsg_Wflat (R : w.RunData) {σ' : (w.runCrimp R).C → ZMod 2}
    (h : σ' ∈ (w.runCrimp R).Wflat) : liftAsg R σ' ∈ w.Wflat := by
  obtain ⟨h', hf', rfl⟩ := h
  obtain ⟨h, hf, ha, hb⟩ := RunData.runLift _ w R rfl hf'
  refine ⟨h, hf, funext fun j => ?_⟩
  simp only [liftAsg, asg_xOf]
  by_cases hj : j.1 ∈ (w.runCrimp R).C
  · simp only [ext0, dif_pos hj, if_pos hj, add_zero, asg_xOf]
    rw [ha j.1 hj]
    simp only [runCrimp_up R hj]
  · have hjB : j.1 ∈ R.B := by
      by_contra h; exact hj (Finset.mem_sdiff.2 ⟨j.2, h⟩)
    simp only [ext0, dif_neg hj, if_neg hj, zero_add]
    rw [hb j.1 hjB, zero_add]

/-- **(G2)** Directions of the crimped walk are directions of the walk. -/
lemma inDir_run (R : w.RunData) {δ' : (w.runCrimp R).C → ZMod 2}
    (h : (w.runCrimp R).InDir δ') : w.InDir (fun j => (w.runCrimp R).ext0 δ' j.1) := by
  -- the lift maps the affine span into the affine span
  have hmap : (w.runCrimp R).affW ⊆ {σ' | liftAsg R σ' ∈ w.affW} := by
    apply affineSpan_subset
    · intro p hp q hq r hr
      simp only [Set.mem_setOf_eq] at hp hq hr ⊢
      rw [liftAsg_add3]; exact aff_add3 hp hq hr
    · intro σ' hσ'; exact Wflat_subset_affW (liftAsg_Wflat R hσ')
  obtain ⟨h₀', hf₀', -⟩ := exists_flat _ (w.runCrimp R) rfl
  have h₀ : (w.runCrimp R).asg (xOf h₀') ∈ (w.runCrimp R).affW :=
    Wflat_subset_affW ⟨h₀', hf₀', rfl⟩
  have e1 := hmap h₀
  have e2 := hmap (h _ h₀)
  simp only [Set.mem_setOf_eq] at e1 e2
  rw [liftAsg_add] at e2
  have := inDir_of_mem e1 e2
  rwa [← add_assoc, show liftAsg R ((w.runCrimp R).asg (xOf h₀')) +
    liftAsg R ((w.runCrimp R).asg (xOf h₀')) = 0 from by
      funext j; exact zmod2_add_self _, zero_add] at this

/-- The two stackings of a walk with two creases. -/
lemma flat_two (h2 : w.C.card = 2) {k : ι} (hk : k ∈ w.C) (a b : ℤ) (hab : a ≠ b) :
    w.IsFlat (fun i => if i = k then a else b) := by
  refine ⟨?_, fun r hr => by rw [rows_eq_empty_of_two h2] at hr; simp at hr⟩
  intro i hi j hj e
  by_cases hik : i = k <;> by_cases hjk : j = k
  · rw [hik, hjk]
  · simp only [hik, hjk, if_true, if_false] at e; exact absurd e hab
  · simp only [hik, hjk, if_true, if_false] at e; exact absurd e.symm hab
  · rw [(two_creases h2 hi hk).resolve_left hik, (two_creases h2 hj hk).resolve_left hjk]

/-- The indicators of two creases of the crimped walk, seen in the walk. -/
lemma ext0_eC (R : w.RunData) {i j : ι} (hi : i ∈ (w.runCrimp R).C) (hj : j ∈ (w.runCrimp R).C) :
    (fun k : w.C => (w.runCrimp R).ext0 ((w.runCrimp R).eC i + (w.runCrimp R).eC j) k.1) =
      w.eC i + w.eC j := by
  funext k
  simp only [ext0, eC, Pi.add_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> first | rfl | simp_all

/-- Consecutive creases of a run are related. -/
lemma inDir_run_chain (R : w.RunData) (h4 : 4 ≤ w.C.card) :
    ∀ m ≤ R.k + 1, w.InDir (w.eC R.A + w.eC (R.t m)) := by
  intro m
  induction m with
  | zero => intro _; exact inDir_refl _
  | succ m ih =>
    intro hm
    have hc := R.crimpOK_t (i := m + 1) (by omega) hm h4
    have := inDir_crimp hc
    rw [R.prv_t_succ] at this
    exact inDir_trans (ih (by omega)) this

/-- **Two creases of one block of the recursion differ by a direction of `aff W_flat`.** -/
theorem inDir_of_lab : ∀ {w : Walk ι α} (c : Chain w) {i j : ι}, i ∈ w.C → j ∈ w.C →
    c.lab i = c.lab j → w.InDir (w.eC i + w.eC j) := by
  intro w c
  induction c with
  | @base w h =>
    intro i j hi hj _
    have hstep : ∀ k ∈ w.C, w.InDir (w.eC k + w.eC (nxt w.C k)) := by
      intro k hk
      by_cases h2 : w.C.card = 2
      · have f1 := flat_two h2 hk 0 1 (by norm_num)
        have f2 := flat_two h2 hk 1 0 (by norm_num)
        have key : w.asg (xOf fun i => if i = k then (0 : ℤ) else 1) +
            w.asg (xOf fun i => if i = k then (1 : ℤ) else 0) = w.eC k + w.eC (nxt w.C k) := by
          funext x
          have hn := w.nxt_ne hk
          simp only [Pi.add_apply, asg_xOf, eC, xOf]
          rcases two_creases h2 x.2 hk with e | e
          · rw [e]
            simp [hn, Ne.symm hn]
            generalize (if w.up k then (0 : ZMod 2) else 1) = u; revert u; decide
          · have hpn : prv w.C k = nxt w.C k :=
              ((two_creases h2 (w.nxt_mem hk) hk).resolve_left hn).symm
            have hxn : x.1 = nxt w.C k := e.trans hpn
            have hnn : nxt w.C (nxt w.C k) = k :=
              (two_creases h2 (w.nxt_mem (w.nxt_mem hk)) hk).resolve_right
                (fun f => w.nxt_ne (w.nxt_mem hk) (f.trans hpn))
            rw [hxn, hnn]
            simp [hn, Ne.symm hn]
            generalize (if w.up (nxt w.C k) then (0 : ZMod 2) else 1) = u; revert u; decide
        rw [← key]
        exact inDir_of_mem (Wflat_subset_affW ⟨_, f1, rfl⟩) (Wflat_subset_affW ⟨_, f2, rfl⟩)
      · have h4 : 4 ≤ w.C.card := by
          have := w.two_le; obtain ⟨m, hm⟩ := card_even (w := w); omega
        have hc : w.CrimpOK (nxt w.C k) := ⟨w.nxt_mem hk, h4,
          le_of_eq (h _ (w.nxt_mem hk) _ (w.prv_mem (w.nxt_mem hk))),
          le_of_eq (h _ (w.nxt_mem hk) _ (w.nxt_mem (w.nxt_mem hk)))⟩
        have := inDir_crimp hc
        rwa [prv_nxt hk] at this
    have := cycle_induction (fun x => w.InDir (w.eC i + w.eC x)) hi (inDir_refl i)
      (fun k hk hik => inDir_trans hik (hstep k hk)) j hj
    exact this
  | @step w R c ih =>
    intro i j hi hj hlab
    simp only [Chain.lab] at hlab
    by_cases hk : Even R.k
    · simp only [if_pos hk] at hlab
      have h4 := R.four_le (Or.inr hk)
      have hA := A_not_C' R hk
      have hBrel : ∀ x ∈ R.B, w.InDir (w.eC R.A + w.eC x) := by
        intro x hx
        obtain ⟨m, -, hm, rfl⟩ := R.mem_B.1 hx
        exact inDir_run_chain R h4 m hm
      by_cases hiB : i ∈ R.B <;> by_cases hjB : j ∈ R.B
      · exact inDir_trans (inDir_symm (hBrel i hiB)) (hBrel j hjB)
      · rw [if_pos hiB, if_neg hjB] at hlab
        exact absurd (hlab ▸ c.lab_mem (R.mem_C'.2 ⟨hj, hjB⟩)) hA
      · rw [if_neg hiB, if_pos hjB] at hlab
        exact absurd (hlab.symm ▸ c.lab_mem (R.mem_C'.2 ⟨hi, hiB⟩)) hA
      · rw [if_neg hiB, if_neg hjB] at hlab
        have hi' := R.mem_C'.2 ⟨hi, hiB⟩
        have hj' := R.mem_C'.2 ⟨hj, hjB⟩
        have := inDir_run R (ih hi' hj' hlab)
        rwa [ext0_eC R hi' hj'] at this
    · simp only [if_neg hk] at hlab
      have h4 := R.four_le (Or.inl (by
        rcases Nat.even_or_odd R.k with h | ⟨q, hq⟩ <;> [exact absurd h hk; omega]))
      have hA' := A_mem_C' R hk
      have hred : ∀ x ∈ w.C, w.InDir (w.eC x + w.eC (if x ∈ R.B then R.A else x)) := by
        intro x hx
        split_ifs with hxB
        · obtain ⟨m, -, hm, rfl⟩ := R.mem_B.1 hxB
          exact inDir_symm (inDir_run_chain R h4 m hm)
        · exact inDir_refl x
      have hmem : ∀ x ∈ w.C, (if x ∈ R.B then R.A else x) ∈ (w.runCrimp R).C := by
        intro x hx; split_ifs with hxB
        · exact hA'
        · exact R.mem_C'.2 ⟨hx, hxB⟩
      have hlab' : c.lab (if i ∈ R.B then R.A else i) = c.lab (if j ∈ R.B then R.A else j) := by
        split_ifs at hlab ⊢ <;> exact hlab
      have := inDir_run R (ih (hmem i hi) (hmem j hj) hlab')
      rw [ext0_eC R (hmem i hi) (hmem j hj)] at this
      exact inDir_trans (hred i hi) (inDir_trans this (inDir_symm (hred j hj)))

lemma bsum_add (r : ι → ι → Prop) (σ τ : w.C → ZMod 2) (j₀ : ι) :
    w.bsum r (σ + τ) j₀ = w.bsum r σ j₀ + w.bsum r τ j₀ := by
  unfold bsum; rw [ext0_add]; simp only [Pi.add_apply]; exact Finset.sum_add_distrib

lemma bsum_eC (r : ι → ι → Prop) {x : ι} (hx : x ∈ w.C) (j₀ : ι) :
    w.bsum r (w.eC x) j₀ = if r j₀ x then 1 else 0 := by
  have e : ∀ j, w.ext0 (w.eC x) j = if j = x then 1 else 0 := by
    intro j; unfold ext0 eC
    by_cases hj : j ∈ w.C
    · simp only [dif_pos hj]
    · rw [dif_neg hj, if_neg (fun h : j = x => hj (h ▸ hx))]
  unfold bsum
  simp_rw [e]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, hx, true_and]

lemma zmod2_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert h; generalize x = u; revert u; decide

/-- **Vectors with zero sum on every block are directions of `aff W_flat`.** -/
theorem inDir_of_blocks (c : Chain w) : ∀ (n : ℕ) (δ : w.C → ZMod 2),
    (Finset.univ.filter fun j => δ j = 1).card = n →
    (∀ j₀ ∈ w.C, w.bsum (labRel c) δ j₀ = 0) → w.InDir δ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro δ hn hδ
  by_cases h0 : ∀ j, δ j = 0
  · rw [show δ = 0 from funext h0]; exact inDir_zero
  push_neg at h0
  obtain ⟨i, hi⟩ := h0
  have hi1 : δ i = 1 := zmod2_eq_one hi
  -- a second crease of the block of `i` where `δ` is one
  obtain ⟨j, hjC, hjb, hji, hj1⟩ :
      ∃ j ∈ w.C, labRel c i.1 j ∧ j ≠ i.1 ∧ w.ext0 δ j = 1 := by
    by_contra hne
    push_neg at hne
    have hs : ∑ j ∈ w.C.filter (labRel c i.1), w.ext0 δ j = w.ext0 δ i.1 := by
      apply Finset.sum_eq_single i.1
      · intro j hj hji
        obtain ⟨hjC, hjb⟩ := Finset.mem_filter.1 hj
        by_contra h1
        exact hne j hjC hjb hji (zmod2_eq_one h1)
      · intro h; exact absurd (Finset.mem_filter.2 ⟨i.2, (show labRel c i.1 i.1 from rfl)⟩) h
    have := hδ i.1 i.2
    unfold bsum at this
    rw [hs, show w.ext0 δ i.1 = δ i from ext0_mem δ i, hi1] at this
    exact one_ne_zero this
  set j' : w.C := ⟨j, hjC⟩
  have hj'1 : δ j' = 1 := by rw [← ext0_mem δ j']; exact hj1
  have hj'i : j' ≠ i := fun h => hji (congrArg Subtype.val h)
  set δ' := δ + w.eC i.1 + w.eC j
  -- `δ'` still has zero sums on the blocks
  have hδ' : ∀ j₀ ∈ w.C, w.bsum (labRel c) δ' j₀ = 0 := by
    intro j₀ hj₀
    rw [bsum_add, bsum_add, hδ j₀ hj₀, bsum_eC _ i.2, bsum_eC _ hjC]
    have : labRel c j₀ i.1 ↔ labRel c j₀ j := by
      unfold labRel at hjb ⊢; rw [hjb]
    by_cases h : labRel c j₀ i.1
    · rw [if_pos h, if_pos (this.1 h)]; decide
    · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; decide
  -- and two fewer ones
  have hsupp : (Finset.univ.filter fun k => δ' k = 1) =
      ((Finset.univ.filter fun k => δ k = 1).erase i).erase j' := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    have hval : δ' k = δ k + (if k.1 = i.1 then 1 else 0) + (if k.1 = j then 1 else 0) := rfl
    rw [hval]
    by_cases hki : k = i
    · have e1 : k.1 = i.1 := congrArg Subtype.val hki
      have e2 : k.1 ≠ j := fun h => hji (h ▸ e1)
      rw [if_pos e1, if_neg e2, hki, hi1]
      simp only [ne_eq, not_true_eq_false, false_and, and_false, iff_false]
      decide
    · by_cases hkj : k = j'
      · have e1 : k.1 = j := congrArg Subtype.val hkj
        have e2 : k.1 ≠ i.1 := fun h => hji (e1 ▸ h)
        rw [if_neg e2, if_pos e1, hkj, hj'1]
        simp only [ne_eq, not_true_eq_false, false_and, iff_false]
        decide
      · have e1 : k.1 ≠ i.1 := fun h => hki (Subtype.ext h)
        have e2 : k.1 ≠ j := fun h => hkj (Subtype.ext h)
        rw [if_neg e1, if_neg e2, add_zero, add_zero]
        simp [hki, hkj]
  have hcard : (Finset.univ.filter fun k => δ' k = 1).card < n := by
    rw [hsupp, ← hn]
    have hm1 : i ∈ Finset.univ.filter fun k => δ k = 1 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi1⟩
    have hm2 : j' ∈ (Finset.univ.filter fun k => δ k = 1).erase i :=
      Finset.mem_erase.2 ⟨hj'i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'1⟩⟩
    rw [Finset.card_erase_of_mem hm2, Finset.card_erase_of_mem hm1]
    have := Finset.card_pos.2 ⟨i, hm1⟩
    omega
  have h1 := ih _ hcard δ' rfl hδ'
  have h2 := inDir_of_lab c i.2 hjC hjb
  have := inDir_add h1 h2
  rwa [show δ' + (w.eC i.1 + w.eC j) = δ by
    funext k; simp only [δ', Pi.add_apply]
    generalize δ k = a; generalize w.eC i.1 k = b; generalize w.eC j k = d
    revert a b d; decide] at this

/-- `W₄ ⊆ aff W_flat`. -/
theorem W4_subset_affW (c : Chain w) : c.W4 ⊆ w.affW := by
  obtain ⟨σ₀, hf₀, h₄₀⟩ := exists_base c
  intro σ hσ
  rw [W4_eq_part c h₄₀] at hσ
  have hδ : ∀ j₀ ∈ w.C, w.bsum (labRel c) (σ + σ₀) j₀ = 0 := by
    intro j₀ hj₀; rw [bsum_add, hσ j₀ hj₀]; exact zmod2_add_self _
  have := inDir_of_blocks c _ (σ + σ₀) rfl hδ σ₀ (Wflat_subset_affW hf₀)
  rwa [show σ₀ + (σ + σ₀) = σ by
    funext k; simp only [Pi.add_apply]
    generalize σ k = a; generalize σ₀ k = b; revert a b; decide] at this

lemma ext0_asg (x : ι → ι → ZMod 2) {j : ι} (hj : j ∈ w.C) :
    w.ext0 (w.asg x) j = x j (nxt w.C j) + if w.up j then 0 else 1 := by
  simp only [ext0, dif_pos hj]; rfl

/-- **Lemma 3 (easy half).** Every solution satisfies the equation of every component. -/
theorem Wlin_subset_comp {σ₀ : w.C → ZMod 2} (h₀ : σ₀ ∈ w.Wlin) :
    w.Wlin ⊆ w.Part w.SameComp σ₀ := by
  rintro _ ⟨x, hx, hsx, rfl⟩ j₀ hj₀
  obtain ⟨x₀, hx₀, hsx₀, rfl⟩ := h₀
  unfold bsum
  rw [Finset.sum_congr rfl fun j hj => ext0_asg x (Finset.mem_of_mem_filter j hj),
    Finset.sum_congr rfl fun j hj => ext0_asg x₀ (Finset.mem_of_mem_filter j hj),
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  by_cases h2 : w.C.card = 2
  · have hall : w.C.filter (w.SameComp j₀) = w.C := by
      ext j; simp only [Finset.mem_filter, and_iff_left_iff_imp]
      exact fun hj => sameComp_of_two h2 hj₀ hj
    rw [hall, sum_nxt_two h2 hx, sum_nxt_two h2 hx₀]
  · exact sum_comp_eq hx hx₀ hsx hsx₀ (by have := w.two_le; omega) j₀

/-- **The components refine the blocks**, so the component equations imply those of `W₄`. -/
theorem comp_subset_part (c : Chain w) (σ₀ : w.C → ZMod 2) :
    w.Part w.SameComp σ₀ ⊆ w.Part (labRel c) σ₀ := by
  intro σ hσ j₀ hj₀
  set δ := σ + σ₀
  have hδc : ∀ j₁ ∈ w.C, w.bsum w.SameComp δ j₁ = 0 := by
    intro j₁ hj₁; rw [bsum_add, hσ j₁ hj₁]; exact zmod2_add_self _
  suffices h : w.bsum (labRel c) δ j₀ = 0 by
    rw [bsum_add] at h
    generalize w.bsum (labRel c) σ j₀ = a at h ⊢
    generalize w.bsum (labRel c) σ₀ j₀ = b at h ⊢
    revert a b; decide
  -- the representative of the component of a crease
  let rep : ι → ι := fun j =>
    if h : (w.C.filter (w.SameComp j)).Nonempty then (w.C.filter (w.SameComp j)).min' h else j
  have hrep : ∀ j ∈ w.C, rep j ∈ w.C ∧ w.SameComp j (rep j) := by
    intro j hj
    have hne : (w.C.filter (w.SameComp j)).Nonempty := ⟨j, Finset.mem_filter.2 ⟨hj, conn_refl _⟩⟩
    have := Finset.min'_mem _ hne
    simp only [rep, dif_pos hne]
    exact Finset.mem_filter.1 this
  have hrep_eq : ∀ j ∈ w.C, ∀ j' ∈ w.C, w.SameComp j j' → rep j = rep j' := by
    intro j hj j' hj' h
    have : w.C.filter (w.SameComp j) = w.C.filter (w.SameComp j') := by
      ext x; simp only [Finset.mem_filter]
      exact ⟨fun ⟨hx, h'⟩ => ⟨hx, conn_trans (conn_symm h) h'⟩,
        fun ⟨hx, h'⟩ => ⟨hx, conn_trans h h'⟩⟩
    have hne : (w.C.filter (w.SameComp j')).Nonempty :=
      ⟨j', Finset.mem_filter.2 ⟨hj', conn_refl _⟩⟩
    simp only [rep]
    rw [this, dif_pos hne, dif_pos hne]
  set S := w.C.filter (labRel c j₀)
  unfold bsum
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image rep) (g := rep)
    (fun x hx => Finset.mem_image_of_mem rep hx)]
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨j₁, hj₁, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨hj₁C, hj₁b⟩ := Finset.mem_filter.1 hj₁
  have : S.filter (fun x => rep x = rep j₁) = w.C.filter (w.SameComp j₁) := by
    ext x
    simp only [S, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, -⟩, hr⟩
      refine ⟨hx, ?_⟩
      have h1 := (hrep x hx).2; have h2 := (hrep j₁ hj₁C).2
      rw [hr] at h1
      exact conn_trans h2 (conn_symm h1)
    · rintro ⟨hx, h⟩
      refine ⟨⟨hx, ?_⟩, (hrep_eq j₁ hj₁C x hx h).symm⟩
      unfold labRel at hj₁b ⊢
      rw [hj₁b]; exact Chain.lab_eq_of_sameComp c hj₁C hx h
  rw [this]
  exact hδc j₁ hj₁C

/-- **Theorem 4.**  At every vertex (every closed walk), for every run of Hull's recursion,
the assignments induced by the solutions of the taco–tortilla and taco–taco rows form the
affine hull over `𝔽₂` of the flat-foldable ones, and they are given by Hull's recursion read
modulo four: `W_lin = aff W_flat = W₄`. -/
theorem theorem3 (c : Chain w) : w.Wlin = c.W4 ∧ w.affW = w.Wlin := by
  obtain ⟨σ₀, hf₀, h₄₀⟩ := exists_base c
  have h₀ : σ₀ ∈ w.Wlin := Wflat_subset_Wlin hf₀
  have i1 := W4_subset_affW c
  have i2 := affW_subset_Wlin (w := w)
  have i3 : w.Wlin ⊆ c.W4 := by
    rw [W4_eq_part c h₄₀]; exact (Wlin_subset_comp h₀).trans (comp_subset_part c σ₀)
  exact ⟨subset_antisymm i3 (i1.trans i2), subset_antisymm i2 (i3.trans i1)⟩

end Walk

end Origami
