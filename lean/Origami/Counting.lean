import Origami.Theorem3
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finite.Basic

/-!
# Counting: `|W_lin| = 2^(n-1-E)` and `γ = E + 1` (Theorem 4 and Lemma 3)

* The labels of the recursion are idempotent, and there are `E + 1` of them.
* The assignments with prescribed sums over the blocks of a partition into `b` blocks are
  `2^(n - b)` (rank–nullity over `𝔽₂`).
* By Theorem 4 the components of `H_v` containing adjacent pairs are exactly the blocks of
  the recursion, so `γ = E + 1` and `W_lin` has `2^(n - γ)` elements (Lemma 3).
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

namespace Chain

/-- Every label is the label of itself. -/
lemma lab_lab : ∀ {w : Walk ι α} (c : Chain w) {j : ι}, j ∈ w.C → c.lab (c.lab j) = c.lab j
  | w, base _, _, _ => rfl
  | w, step R c, j, hj => by
    have hsub : (w.runCrimp R).C ⊆ w.C := Finset.sdiff_subset
    by_cases hk : Even R.k
    · have hA := A_not_C' R hk
      have hAB : R.A ∈ R.B := R.t_mem_B (i := 0) (by simp [hk]) (by omega)
      simp only [lab, if_pos hk]
      by_cases hjB : j ∈ R.B
      · rw [if_pos hjB, if_pos hAB]
      · have hj' := R.mem_C'.2 ⟨hj, hjB⟩
        have hl := c.lab_mem hj'
        rw [if_neg hjB, if_neg (fun h => (Finset.mem_sdiff.1 hl).2 h), c.lab_lab hj']
    · have hA' := A_mem_C' R hk
      simp only [lab, if_neg hk]
      have key : ∀ x ∈ (w.runCrimp R).C, (if c.lab x ∈ R.B then c.lab R.A else c.lab (c.lab x)) =
          c.lab x := by
        intro x hx
        have hl := c.lab_mem hx
        rw [if_neg (fun h => (Finset.mem_sdiff.1 hl).2 h), c.lab_lab hx]
      by_cases hjB : j ∈ R.B
      · rw [if_pos hjB]; exact key _ hA'
      · rw [if_neg hjB]; exact key _ (R.mem_C'.2 ⟨hj, hjB⟩)

/-- **There are `E + 1` blocks.** -/
theorem card_labels : ∀ {w : Walk ι α} (c : Chain w), (w.C.image c.lab).card = c.E + 1
  | w, base _ => by
    simp only [lab, E]
    rw [Finset.image_const w.nonempty, Finset.card_singleton]
  | w, step R c => by
    have IH := c.card_labels
    by_cases hk : Even R.k
    · have hA := A_not_C' R hk
      have hAB : R.A ∈ R.B := R.t_mem_B (i := 0) (by simp [hk]) (by omega)
      have e : w.C.image (step R c).lab = insert R.A ((w.runCrimp R).C.image c.lab) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_insert, lab, if_pos hk]
        constructor
        · rintro ⟨j, hj, rfl⟩
          by_cases hjB : j ∈ R.B
          · left; rw [if_pos hjB]
          · right; exact ⟨j, R.mem_C'.2 ⟨hj, hjB⟩, by rw [if_neg hjB]⟩
        · rintro (rfl | ⟨j, hj, rfl⟩)
          · exact ⟨R.A, R.hA, by rw [if_pos hAB]⟩
          · exact ⟨j, (Finset.mem_sdiff.1 hj).1, by rw [if_neg (Finset.mem_sdiff.1 hj).2]⟩
      rw [e, Finset.card_insert_of_notMem, IH]
      · simp only [E, if_pos hk]
      · intro h
        obtain ⟨j, hj, hl⟩ := Finset.mem_image.1 h
        exact hA (hl ▸ c.lab_mem hj)
    · have hA' := A_mem_C' R hk
      have e : w.C.image (step R c).lab = (w.runCrimp R).C.image c.lab := by
        ext x
        simp only [Finset.mem_image, lab, if_neg hk]
        constructor
        · rintro ⟨j, hj, rfl⟩
          by_cases hjB : j ∈ R.B
          · exact ⟨R.A, hA', by rw [if_pos hjB]⟩
          · exact ⟨j, R.mem_C'.2 ⟨hj, hjB⟩, by rw [if_neg hjB]⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j, (Finset.mem_sdiff.1 hj).1, by rw [if_neg (Finset.mem_sdiff.1 hj).2]⟩
      rw [e, IH]
      simp only [E, if_neg hk, add_zero]

end Chain

/-! ### Counting a space cut out by block sums -/

/-- The block sums, as a linear map to functions on the labels. -/
noncomputable def blockMap (w : Walk ι α) (lab : ι → ι) :
    (w.C → ZMod 2) →ₗ[ZMod 2] (w.C.image lab → ZMod 2) where
  toFun δ := fun ℓ => ∑ j ∈ (Finset.univ.filter fun j : w.C => lab j.1 = ℓ.1), δ j
  map_add' δ δ' := by funext ℓ; simp [Finset.sum_add_distrib]
  map_smul' a δ := by funext ℓ; simp [Finset.mul_sum]

/-- The block sums are onto, when every label labels itself. -/
lemma blockMap_surjective (lab : ι → ι) (hlab : ∀ j ∈ w.C, lab j ∈ w.C)
    (hidem : ∀ j ∈ w.C, lab (lab j) = lab j) : Function.Surjective (w.blockMap lab) := by
  intro τ
  -- put the value of each block on its label
  refine ⟨fun j => if h : lab j.1 = j.1 then τ ⟨j.1, Finset.mem_image.2 ⟨j.1, j.2, h⟩⟩ else 0, ?_⟩
  funext ℓ
  obtain ⟨j₀, hj₀, hℓ⟩ := Finset.mem_image.1 ℓ.2
  simp only [blockMap, LinearMap.coe_mk, AddHom.coe_mk]
  have hℓC : ℓ.1 ∈ w.C := hℓ ▸ hlab j₀ hj₀
  have hℓℓ : lab ℓ.1 = ℓ.1 := by rw [← hℓ]; exact hidem j₀ hj₀
  rw [Finset.sum_eq_single ⟨ℓ.1, hℓC⟩]
  · simp only [hℓℓ, dif_pos]
  · intro j hj hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [dif_neg]
    intro h
    exact hne (Subtype.ext (h.symm.trans hj))
  · intro h; exact absurd (by simp [hℓℓ]) h

/-- `2^(n - b)` assignments have zero sum on each of `b` blocks. -/
lemma card_ker (lab : ι → ι) (hlab : ∀ j ∈ w.C, lab j ∈ w.C)
    (hidem : ∀ j ∈ w.C, lab (lab j) = lab j) :
    Nat.card (LinearMap.ker (w.blockMap lab)) = 2 ^ (w.C.card - (w.C.image lab).card) := by
  have hsurj := blockMap_surjective lab hlab hidem
  have hrank := LinearMap.finrank_range_add_finrank_ker (w.blockMap lab)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at hrank
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  congr 1
  omega

/-- Block sums through the linear map. -/
lemma blockMap_apply (c : Chain w) (σ : w.C → ZMod 2) {j₀ : ι} (hj₀ : j₀ ∈ w.C) :
    w.blockMap c.lab σ ⟨c.lab j₀, Finset.mem_image_of_mem _ hj₀⟩ = w.bsum (labRel c) σ j₀ := by
  simp only [blockMap, LinearMap.coe_mk, AddHom.coe_mk, bsum]
  rw [sum_subtype_filter σ (fun j => c.lab j = c.lab j₀)]
  congr 1
  ext j; simp only [Finset.mem_filter, labRel]; exact and_congr_right fun _ => eq_comm

/-- Two finite images with the same fibres have the same size. -/
lemma card_image_eq_of_fibers {β γ : Type*} [DecidableEq β] [DecidableEq γ] {s : Finset ι}
    {f : ι → β} {g : ι → γ} (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  set P := s.image fun x => (f x, g x)
  have hf : (s.image f).card = P.card := by
    rw [show s.image f = P.image Prod.fst by simp only [P, Finset.image_image]; rfl]
    apply Finset.card_image_of_injOn
    intro p hp q hq e
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hq)
    simp only at e
    exact Prod.ext e ((h x hx y hy).1 e)
  have hg : (s.image g).card = P.card := by
    rw [show s.image g = P.image Prod.snd by simp only [P, Finset.image_image]; rfl]
    apply Finset.card_image_of_injOn
    intro p hp q hq e
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hq)
    simp only at e
    exact Prod.ext ((h x hx y hy).2 e) e
  rw [hf, hg]

/-- **Theorem 4 (dimension) and Lemma 3.**  For every run of Hull's recursion, `W_lin` has
`2^(n-1-E)` elements, the components of `H_v` containing adjacent pairs are exactly the blocks
of the recursion, and `γ = E + 1`; in particular `E` does not depend on the choice of runs and
`|W_lin| = 2^(n-γ)`. -/
theorem card_Wlin (c : Chain w) :
    w.Wlin.ncard = 2 ^ (w.C.card - 1 - c.E) ∧ w.gamma = c.E + 1 ∧
      (∀ i ∈ w.C, ∀ j ∈ w.C, w.SameComp i j ↔ c.lab i = c.lab j) := by
  obtain ⟨σ₀, hf₀, h₄₀⟩ := exists_base c
  have h₀ : σ₀ ∈ w.Wlin := Wflat_subset_Wlin hf₀
  have hW : w.Wlin = w.Part (labRel c) σ₀ := by rw [(theorem3 c).1, W4_eq_part c h₄₀]
  -- the blocks are the components
  have hcomp : ∀ i ∈ w.C, ∀ j ∈ w.C, w.SameComp i j ↔ c.lab i = c.lab j := by
    intro i hi j hj
    refine ⟨Chain.lab_eq_of_sameComp c hi hj, fun hl => ?_⟩
    set σ := σ₀ + w.eC i + w.eC j
    have hσ : σ ∈ w.Part (labRel c) σ₀ := by
      intro j₀ hj₀
      rw [bsum_add, bsum_add, bsum_eC _ hi, bsum_eC _ hj]
      have : labRel c j₀ i ↔ labRel c j₀ j := by unfold labRel; rw [hl]
      by_cases h : labRel c j₀ i
      · rw [if_pos h, if_pos (this.1 h)]
        generalize w.bsum (labRel c) σ₀ j₀ = u; revert u; decide
      · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; simp
    have := Wlin_subset_comp h₀ (hW ▸ hσ) i hi
    have hii : w.SameComp i i := conn_refl _
    rw [bsum_add, bsum_add, bsum_eC _ hi, bsum_eC _ hj, if_pos hii] at this
    by_contra hne
    rw [if_neg hne] at this
    generalize w.bsum w.SameComp σ₀ i = u at this; revert u this; decide
  refine ⟨?_, ?_, hcomp⟩
  · -- `W_lin` is a translate of the kernel of the block sums
    have hlab : ∀ j ∈ w.C, c.lab j ∈ w.C := fun j hj => c.lab_mem hj
    have hidem : ∀ j ∈ w.C, c.lab (c.lab j) = c.lab j := fun j hj => c.lab_lab hj
    have hker := card_ker c.lab hlab hidem
    rw [Chain.card_labels] at hker
    have himg : w.Wlin = (fun δ => σ₀ + δ) '' (LinearMap.ker (w.blockMap c.lab) : Set _) := by
      rw [hW]
      ext σ
      simp only [Part, Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
      constructor
      · intro hσ
        have hk0 : w.blockMap c.lab (σ + σ₀) = 0 := by
          funext ℓ
          obtain ⟨j₀, hj₀, hℓ⟩ := Finset.mem_image.1 ℓ.2
          have : ℓ = ⟨c.lab j₀, Finset.mem_image_of_mem _ hj₀⟩ := Subtype.ext hℓ.symm
          rw [this, blockMap_apply c _ hj₀, bsum_add, hσ j₀ hj₀]
          exact zmod2_add_self _
        have hadd : σ₀ + (σ + σ₀) = σ := by
          funext k; simp only [Pi.add_apply]
          generalize σ k = a; generalize σ₀ k = b; revert a b; decide
        exact ⟨σ + σ₀, hk0, hadd⟩
      · rintro ⟨δ, hδ, rfl⟩ j₀ hj₀
        have := congrFun hδ ⟨c.lab j₀, Finset.mem_image_of_mem _ hj₀⟩
        rw [blockMap_apply c _ hj₀, Pi.zero_apply] at this
        rw [bsum_add, this, add_zero]
    rw [himg, Set.ncard_image_of_injective _ (add_right_injective σ₀), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, hker]
    congr 1; omega
  · -- `γ` counts the blocks
    unfold gamma
    rw [← Chain.card_labels c]
    apply card_image_eq_of_fibers
    intro x hx y hy
    rw [← sameComp_iff_quot]
    exact hcomp x hx y hy

end Walk

end Origami
