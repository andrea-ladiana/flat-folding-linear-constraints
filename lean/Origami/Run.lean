import Origami.Components
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Runs of smallest sectors and their crimps (Section 7 of the paper)

A *run* is a maximal sequence `f_a, …, f_{a+k}` of consecutive sectors of the smallest angle
`α`, between two larger sectors `f_A` and `f_Z`.  We describe it by the crease `A` ending
`f_A` and the length `k`: the creases of the run are `t i = nxtⁱ A` for `0 ≤ i ≤ k + 1`, the
run sectors end at `t 1, …, t (k+1)`, and `f_Z` ends at `t (k+2)`.

* For `k` even the crimp deletes the `k + 2` creases `t 0, …, t (k+1)`; `f_A`, the run and
  `f_Z` merge into one sector, which keeps the name `Z = t (k+2)`.
* For `k` odd the crimp deletes the `k + 1` creases `t 1, …, t (k+1)`; the crease `A = t 0`
  survives as the crease `e_⋆` between `f_A` and `f_Z`.

Replacing every position by its opposite (`refl`) changes no row; it lets us assume that the
crease `A` is a maximum, as the paper does.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-! ### Reflection -/

/-- The walk with every position replaced by its opposite. -/
def refl (w : Walk ι α) : Walk ι α where
  C := w.C
  c := fun k => - w.c k
  two_le := w.two_le
  zig := by
    intro k hk
    rcases w.zig k hk with h | h
    · right; exact ⟨neg_lt_neg h.1, neg_lt_neg h.2⟩
    · left; exact ⟨neg_lt_neg h.1, neg_lt_neg h.2⟩

@[simp] lemma refl_C : w.refl.C = w.C := rfl
@[simp] lemma refl_c (k : ι) : w.refl.c k = - w.c k := rfl

lemma refl_lo (g : ι) : w.refl.lo g = - w.hi g := by
  unfold lo hi; simp only [refl_C, refl_c]; rw [min_neg_neg]

lemma refl_hi (g : ι) : w.refl.hi g = - w.lo g := by
  unfold lo hi; simp only [refl_C, refl_c]; rw [max_neg_neg]

lemma refl_len (g : ι) : w.refl.len g = w.len g := by
  unfold len; rw [refl_lo, refl_hi]; ring

lemma refl_up {k : ι} (hk : k ∈ w.C) : w.refl.up k ↔ ¬ w.up k := by
  unfold up; simp only [refl_C, refl_c, neg_lt_neg_iff]
  rw [← not_up_iff hk]; rfl

lemma refl_rows : w.refl.rows = w.rows := by
  have htt : ∀ q g, (w.refl.lo g < w.refl.c q ∧ w.refl.c q < w.refl.hi g) ↔
      (w.lo g < w.c q ∧ w.c q < w.hi g) := by
    intro q g; rw [refl_lo, refl_hi, refl_c, neg_lt_neg_iff, neg_lt_neg_iff]; tauto
  unfold rows ttRows tcRows
  congr 1
  · congr 1
    ext p; simp only [Finset.mem_filter, refl_C, htt]
  · congr 1
    ext p
    simp only [Finset.mem_filter, refl_C, refl_c, neg_inj, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      exact ⟨⟨h1, h2⟩, h3, h4, by rw [refl_up h1, refl_up h2] at h5; tauto⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      exact ⟨⟨h1, h2⟩, h3, h4, by rw [refl_up h1, refl_up h2]; tauto⟩

lemma refl_linked : w.refl.Linked = w.Linked := by
  funext u v; unfold Linked; rw [refl_rows]

lemma refl_conn : w.refl.Conn = w.Conn := by unfold Conn; rw [refl_linked]

lemma refl_sameComp : w.refl.SameComp = w.SameComp := by
  funext k l; unfold SameComp adj; rw [refl_conn]; rfl

/-! ### Runs -/

/-- A maximal run of `k + 1` sectors of the smallest angle, after the sector `f_A`. -/
structure RunData (w : Walk ι α) where
  A : ι
  k : ℕ
  hA : A ∈ w.C
  hcard : k + 3 ≤ w.C.card
  hmin : ∀ g ∈ w.C, w.len (nxt w.C A) ≤ w.len g
  hrun : ∀ i ≤ k, w.len ((nxt w.C)^[i + 1] A) = w.len (nxt w.C A)
  hbigA : w.len (nxt w.C A) < w.len A
  hbigZ : w.len (nxt w.C A) < w.len ((nxt w.C)^[k + 2] A)

namespace RunData

variable (R : w.RunData)

/-- The `i`-th crease of the run. -/
abbrev t (i : ℕ) : ι := (nxt w.C)^[i] R.A

/-- The smallest angle. -/
abbrev al : α := w.len (nxt w.C R.A)

lemma t_mem (i : ℕ) : R.t i ∈ w.C := iterate_mem R.hA i

lemma t_succ (i : ℕ) : R.t (i + 1) = nxt w.C (R.t i) := Function.iterate_succ_apply' _ _ _

lemma t_zero : R.t 0 = R.A := rfl

lemma prv_t_succ (i : ℕ) : prv w.C (R.t (i + 1)) = R.t i := prv_iterate_succ R.hA i

lemma t_inj {i j : ℕ} (hi : i < w.C.card) (hj : j < w.C.card) (h : R.t i = R.t j) : i = j :=
  iterate_inj R.hA hi hj h

lemma card_even_ge : (Even R.k → R.k + 4 ≤ w.C.card) := by
  intro hk
  obtain ⟨m, hm⟩ := card_even (w := w)
  obtain ⟨j, hj⟩ := hk
  have := R.hcard
  omega

/-- The creases deleted by the crimp. -/
def B : Finset ι :=
  if Even R.k then (Finset.range (R.k + 2)).image R.t
  else (Finset.Ico 1 (R.k + 2)).image R.t

lemma mem_B {q : ι} : q ∈ R.B ↔ ∃ i, (if Even R.k then 0 else 1) ≤ i ∧ i ≤ R.k + 1 ∧ q = R.t i := by
  unfold B; split_ifs with h
  · simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, Nat.zero_le _, by omega, rfl⟩
    · rintro ⟨i, -, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩; exact ⟨i, hi1, by omega, rfl⟩
    · rintro ⟨i, hi1, hi2, rfl⟩; exact ⟨i, ⟨hi1, by omega⟩, rfl⟩

lemma B_subset : R.B ⊆ w.C := by
  intro q hq
  obtain ⟨i, -, -, rfl⟩ := R.mem_B.1 hq
  exact R.t_mem i

lemma t_mem_B {i : ℕ} (h1 : (if Even R.k then 0 else 1) ≤ i) (h2 : i ≤ R.k + 1) : R.t i ∈ R.B :=
  R.mem_B.2 ⟨i, h1, h2, rfl⟩

lemma t_not_mem_B {i : ℕ} (h : i = R.k + 2 ∨ (i = 0 ∧ ¬ Even R.k) ∨ i + 1 = w.C.card)
    (hi : i < w.C.card) : R.t i ∉ R.B := by
  intro hm
  obtain ⟨j, hj1, hj2, e⟩ := R.mem_B.1 hm
  have := R.t_inj hi (by have := R.hcard; omega) e
  split_ifs at hj1 with hk
  · rcases h with h | ⟨-, h⟩ | h <;> [omega; exact h hk; (have := R.card_even_ge hk; omega)]
  · have := R.hcard
    rcases h with h | ⟨h, -⟩ | h <;> omega

lemma card_B : R.B.card = if Even R.k then R.k + 2 else R.k + 1 := by
  unfold B; split_ifs with h
  · rw [Finset.card_image_of_injOn (fun i hi j hj e => R.t_inj (by
      have := R.card_even_ge h; simp at hi; omega) (by have := R.card_even_ge h; simp at hj; omega) e),
      Finset.card_range]
  · rw [Finset.card_image_of_injOn (fun i hi j hj e => R.t_inj (by
      have := R.hcard; simp at hi; omega) (by have := R.hcard; simp at hj; omega) e),
      Nat.card_Ico]
    omega

/-! #### Positions along the run -/

/-- Along the run the creases alternate between two positions, `c A` and `c A ∓ α`. -/
lemma pos (hup : w.up R.A) : ∀ i ≤ R.k + 1,
    (w.up (R.t i) ↔ Even i) ∧ w.c (R.t i) = if Even i then w.c R.A else w.c R.A - R.al := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · show w.up R.A ↔ Even 0; simp [hup]
    · show w.c R.A = if Even 0 then w.c R.A else w.c R.A - R.al; simp
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hlen : w.len (R.t (i + 1)) = R.al := R.hrun i (by omega)
    have hup' : w.up (R.t (i + 1)) ↔ ¬ w.up (R.t i) := by rw [R.t_succ]; exact up_nxt (R.t_mem i)
    refine ⟨by rw [hup', h1, Nat.even_add_one], ?_⟩
    by_cases he : Even i
    · have hu : w.up (R.t i) := h1.2 he
      have hnu : ¬ w.up (R.t (i + 1)) := fun h => hup'.1 h hu
      rw [len_of_not_up (R.t_mem _) hnu, R.prv_t_succ] at hlen
      rw [if_neg (by rw [Nat.even_add_one]; exact not_not.2 he)]
      rw [if_pos he] at h2
      linarith
    · have hu : ¬ w.up (R.t i) := fun h => he (h1.1 h)
      have hnu : w.up (R.t (i + 1)) := hup'.2 hu
      rw [len_of_up hnu, R.prv_t_succ] at hlen
      rw [if_pos (by rw [Nat.even_add_one]; exact he)]
      rw [if_neg he] at h2
      linarith

lemma al_pos : 0 < R.al := len_pos (w.nxt_mem R.hA)

/-- The sector `f_A` reaches below the run. -/
lemma c_prvA (hup : w.up R.A) : w.c (prv w.C R.A) < w.c R.A - R.al := by
  have := R.hbigA
  rw [len_of_up hup] at this
  linarith

/-- The sector `f_Z` reaches beyond the run, on the side given by the parity of `k`. -/
lemma c_Z (hup : w.up R.A) :
    (Even R.k → w.c R.A < w.c (R.t (R.k + 2)) ∧ w.up (R.t (R.k + 2))) ∧
    (¬ Even R.k → w.c (R.t (R.k + 2)) < w.c R.A - R.al ∧ ¬ w.up (R.t (R.k + 2))) := by
  obtain ⟨h1, h2⟩ := R.pos hup (R.k + 1) le_rfl
  have hZ := R.hbigZ
  have hup' : w.up (R.t (R.k + 2)) ↔ ¬ w.up (R.t (R.k + 1)) := by
    rw [R.t_succ]; exact up_nxt (R.t_mem _)
  constructor
  · intro hk
    have hn : ¬ Even (R.k + 1) := by rw [Nat.even_add_one]; exact not_not.2 hk
    have hu : w.up (R.t (R.k + 2)) := hup'.2 (fun h => hn (h1.1 h))
    rw [len_of_up hu, R.prv_t_succ, h2, if_neg hn] at hZ
    exact ⟨by linarith, hu⟩
  · intro hk
    have hn : Even (R.k + 1) := by rw [Nat.even_add_one]; exact hk
    have hu : ¬ w.up (R.t (R.k + 2)) := fun h => hup'.1 h (h1.2 hn)
    rw [len_of_not_up (R.t_mem _) hu, R.prv_t_succ, h2, if_pos hn] at hZ
    exact ⟨by linarith, hu⟩

/-! #### The crimped walk -/

/-- The crease ending `f_Z`. -/
abbrev Z : ι := R.t (R.k + 2)

/-- The crease preceding `Z` after the crimp: `prv A` for `k` even, `A` for `k` odd. -/
def star : ι := if Even R.k then prv w.C R.A else R.A

lemma prvA_eq : prv w.C R.A = R.t (w.C.card - 1) := prv_eq_iterate R.hA

lemma Z_mem : R.Z ∈ w.C := R.t_mem _

lemma Z_not_mem_B : R.Z ∉ R.B :=
  R.t_not_mem_B (Or.inl rfl) (by have := R.hcard; omega)

lemma star_mem : R.star ∈ w.C := by
  unfold star; split_ifs
  · exact w.prv_mem R.hA
  · exact R.hA

lemma star_not_mem_B : R.star ∉ R.B := by
  unfold star; split_ifs with hk
  · rw [R.prvA_eq]
    exact R.t_not_mem_B (Or.inr (Or.inr (by have := R.hcard; omega)))
      (by have := R.hcard; omega)
  · exact R.t_not_mem_B (Or.inr (Or.inl ⟨rfl, hk⟩)) (by have := R.hcard; omega)

/-- Between `star` and `Z` there are only deleted creases. -/
lemma btw_star_Z : ∀ i ∈ w.C, cbtw R.star i R.Z → i ∈ R.B := by
  intro i hi hb
  unfold star at hb
  split_ifs at hb with hk
  · have h4 := R.card_even_ge hk
    have e : R.Z = (nxt w.C)^[R.k + 2 + 1] (prv w.C R.A) := by
      rw [Function.iterate_succ_apply, nxt_prv R.hA]
    rw [e] at hb
    obtain ⟨j, hj1, hj2, rfl⟩ := between_iterate (w.prv_mem R.hA) (R.k + 2) (by omega) i hi hb
    have : (nxt w.C)^[j] (prv w.C R.A) = R.t (j - 1) := by
      conv_lhs => rw [show j = j - 1 + 1 by omega]
      rw [Function.iterate_succ_apply, nxt_prv R.hA]
    rw [this]
    exact R.t_mem_B (by simp [hk]) (by omega)
  · obtain ⟨j, hj1, hj2, rfl⟩ :=
      between_iterate R.hA (R.k + 1) (by have := R.hcard; omega) i hi hb
    exact R.t_mem_B (by simp [hk]; omega) (by omega)

lemma nxt_star : nxt (w.C \ R.B) R.star = R.Z :=
  nxt_sdiff R.star_mem R.star_not_mem_B R.Z_mem R.Z_not_mem_B R.btw_star_Z

lemma prv_Z : prv (w.C \ R.B) R.Z = R.star :=
  prv_sdiff R.star_mem R.star_not_mem_B R.Z_mem R.Z_not_mem_B R.btw_star_Z

/-- A surviving crease other than `star` keeps its successor. -/
lemma nxt_other {q : ι} (hq : q ∈ w.C) (hqB : q ∉ R.B) (hqs : q ≠ R.star) :
    nxt (w.C \ R.B) q = nxt w.C q := by
  apply nxt_sdiff_of_mem hq hqB
  intro hm
  obtain ⟨i, hi1, hi2, e⟩ := R.mem_B.1 hm
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · -- `nxt q = A`, so `q = prv A`
    subst h0
    have : q = prv w.C R.A := by
      have h1 := prv_nxt (C := w.C) hq; rw [e] at h1; exact h1.symm
    apply hqs; unfold star; split_ifs with hk
    · exact this
    · simp [hk] at hi1
  · have : q = R.t (i - 1) := by
      have h1 := prv_nxt (C := w.C) hq
      rw [e] at h1
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [← h1, R.prv_t_succ]; simp
    by_cases h1 : (if Even R.k then 0 else 1) ≤ i - 1
    · exact hqB (this ▸ R.t_mem_B h1 (by omega))
    · -- then `i = 1`, `k` odd, `q = A = star`
      apply hqs; unfold star
      split_ifs at h1 with hk
      · simp at h1
      · rw [if_neg hk, this, show i - 1 = 0 by omega]; rfl

/-- A surviving crease other than `Z` keeps its predecessor. -/
lemma prv_other {q : ι} (hq : q ∈ w.C) (hqB : q ∉ R.B) (hqZ : q ≠ R.Z) :
    prv (w.C \ R.B) q = prv w.C q := by
  apply prv_sdiff_of_mem hq hqB
  intro hm
  obtain ⟨i, hi1, hi2, e⟩ := R.mem_B.1 hm
  have : q = R.t (i + 1) := by rw [← nxt_prv hq, e, R.t_succ]
  by_cases h2 : i + 1 ≤ R.k + 1
  · exact hqB (this ▸ R.t_mem_B (by split_ifs at hi1 ⊢ <;> omega) h2)
  · exact hqZ (by rw [this, show i + 1 = R.k + 2 by omega])

lemma Z_ne_star : R.Z ≠ R.star := by
  intro h
  unfold star at h
  split_ifs at h with hk
  · rw [R.prvA_eq] at h
    have := R.t_inj (by have := R.hcard; omega) (by have := R.hcard; omega) h
    have := R.card_even_ge hk; omega
  · have := R.t_inj (i := R.k + 2) (j := 0) (by have := R.hcard; omega)
      (by have := R.hcard; omega) h
    omega

/-- Validity of the crimped walk, when `A` is a maximum. -/
lemma zig_crimp_of_up (hup : w.up R.A) : ∀ q ∈ w.C \ R.B,
    (w.c (prv (w.C \ R.B) q) < w.c q ∧ w.c (nxt (w.C \ R.B) q) < w.c q) ∨
    (w.c q < w.c (prv (w.C \ R.B) q) ∧ w.c q < w.c (nxt (w.C \ R.B) q)) := by
  intro q hq
  obtain ⟨hqC, hqB⟩ := Finset.mem_sdiff.1 hq
  have hP := R.c_prvA hup
  have hZ := R.c_Z hup
  have al := R.al_pos
  by_cases hs : q = R.star
  · rw [hs, R.nxt_star, prv_other R R.star_mem R.star_not_mem_B (Ne.symm R.Z_ne_star)]
    unfold star; split_ifs with hk
    · -- `prv A` is a minimum below the run, `Z` a maximum above it
      have hz := (hZ.1 hk).1
      have hmin : ¬ w.up (prv w.C R.A) := by rw [up_prv R.hA]; exact not_not.2 hup
      right
      exact ⟨(not_up_iff (w.prv_mem R.hA)).1 hmin, by linarith⟩
    · have hz := (hZ.2 hk).1
      left; exact ⟨hup, by linarith⟩
  by_cases hz : q = R.Z
  · rw [hz, R.prv_Z, nxt_other R R.Z_mem R.Z_not_mem_B R.Z_ne_star]
    unfold star; split_ifs with hk
    · obtain ⟨h1, h2⟩ := hZ.1 hk
      left; exact ⟨by linarith, (up_iff_nxt R.Z_mem).1 h2⟩
    · obtain ⟨h1, h2⟩ := hZ.2 hk
      right; exact ⟨by linarith, (not_up_iff_nxt R.Z_mem).1 h2⟩
  · rw [R.nxt_other hqC hqB hs, R.prv_other hqC hqB hz]
    exact w.zig q hqC

/-- The same run, in the reflected walk. -/
def refl' : w.refl.RunData where
  A := R.A
  k := R.k
  hA := R.hA
  hcard := R.hcard
  hmin := fun g hg => by rw [refl_len, refl_len]; exact R.hmin g hg
  hrun := fun i hi => by rw [refl_len, refl_len]; exact R.hrun i hi
  hbigA := by rw [refl_len, refl_len]; exact R.hbigA
  hbigZ := by rw [refl_len, refl_len]; exact R.hbigZ

lemma refl'_B : R.refl'.B = R.B := rfl

/-- Validity of the crimped walk. -/
lemma zig_crimp : ∀ q ∈ w.C \ R.B,
    (w.c (prv (w.C \ R.B) q) < w.c q ∧ w.c (nxt (w.C \ R.B) q) < w.c q) ∨
    (w.c q < w.c (prv (w.C \ R.B) q) ∧ w.c q < w.c (nxt (w.C \ R.B) q)) := by
  by_cases hup : w.up R.A
  · exact R.zig_crimp_of_up hup
  · intro q hq
    have := R.refl'.zig_crimp_of_up ((refl_up R.hA).2 hup) q hq
    simp only [refl_C, refl_c, neg_lt_neg_iff, refl'_B] at this
    tauto

lemma card_crimp : 2 ≤ (w.C \ R.B).card := by
  rw [Finset.card_sdiff_of_subset R.B_subset, R.card_B]
  split_ifs with hk
  · have := R.card_even_ge hk; omega
  · have := R.hcard; omega

end RunData

/-- The walk obtained by crimping a run. -/
def runCrimp (w : Walk ι α) (R : w.RunData) : Walk ι α where
  C := w.C \ R.B
  c := w.c
  two_le := R.card_crimp
  zig := R.zig_crimp

@[simp] lemma runCrimp_C (R : w.RunData) : (w.runCrimp R).C = w.C \ R.B := rfl
@[simp] lemma runCrimp_c (R : w.RunData) : (w.runCrimp R).c = w.c := rfl

lemma refl_runCrimp (R : w.RunData) : (w.runCrimp R).refl = w.refl.runCrimp R.refl' := rfl

end Walk

end Origami
