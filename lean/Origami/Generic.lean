import Origami.Counting
import Origami.Pairing

/-!
# Lemma 3, big–little–big, and generic vertices (Theorem 2, Lemma 6, Corollary 1)

Theorem 2 is proved as in the paper, by the gauge of a lowest crease (`Pairing.lean`); a
second proof, through Theorem 4 and Hull's recursion, is kept as `theorem2_hull`.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-- **Lemma 3 (relations are components).**  `W_lin` is cut out by one equation for every
component of `H_v` containing adjacent pairs (the sum of the adjacent variables of the
component is fixed), and it has `2^(n - γ)` elements. -/
theorem lemma4 {σ₀ : w.C → ZMod 2} (h₀ : σ₀ ∈ w.Wlin) :
    w.Wlin = w.Part w.SameComp σ₀ ∧ w.Wlin.ncard = 2 ^ (w.C.card - w.gamma) := by
  obtain ⟨c⟩ := exists_chain _ w rfl
  obtain ⟨hcard, hgam, -⟩ := card_Wlin c
  have h₄ : σ₀ ∈ c.W4 := (theorem3 c).1 ▸ h₀
  refine ⟨subset_antisymm (Wlin_subset_comp h₀) ?_, by rw [hcard, hgam]; congr 1; omega⟩
  rw [(theorem3 c).1, W4_eq_part c h₄]
  exact comp_subset_part c σ₀

/-! ### Big–little–big (Proposition 4) -/

/-- **Proposition 4 (big–little–big).**  If the sector `f_a` is smaller than both its
neighbours, the taco–tortilla rows `(e_{a-1}, f_{a+1})` and `(e_a, f_{a-1})` exist, every
assignment of the layer variables satisfying them has `r_{a-1,a} = r_{a,a+1}`, and the two
creases of `f_a` receive opposite assignments.  No genericity is needed. -/
theorem big_little_big {a : ι} (ha : a ∈ w.C) (h3 : 3 ≤ w.C.card)
    (hA : w.len a < w.len (prv w.C a)) (hZ : w.len a < w.len (nxt w.C a)) :
    w.IsTT (prv w.C a) (nxt w.C a) ∧ w.IsTT a (prv w.C a) ∧
      ∀ x : ι → ι → ZMod 2, w.Antisymm x →
        (Row.tt (prv w.C a) a (nxt w.C a)).eval x = 0 →
        (Row.tt a (nxt w.C a) (prv w.C a)).eval x = 0 →
        x (prv w.C a) a = x a (nxt w.C a) ∧
          w.asg x ⟨prv w.C a, w.prv_mem ha⟩ ≠ w.asg x ⟨a, ha⟩ := by
  have hPa := w.prv_mem ha
  have hZa := w.nxt_mem ha
  have hPP := w.prv_mem hPa
  have upa : w.up a ↔ ¬ w.up (prv w.C a) := by
    have := up_nxt hPa; rwa [nxt_prv ha] at this
  have upZ : w.up (nxt w.C a) ↔ ¬ w.up a := up_nxt ha
  -- positions
  have pos : w.IsTT (prv w.C a) (nxt w.C a) ∧ w.IsTT a (prv w.C a) := by
    by_cases hu : w.up (prv w.C a)
    · have hna : ¬ w.up a := fun h => upa.1 h hu
      have hz : w.up (nxt w.C a) := upZ.2 hna
      rw [len_of_not_up ha hna, len_of_up hu] at hA
      rw [len_of_not_up ha hna, len_of_up hz, prv_nxt ha] at hZ
      refine ⟨⟨hPa, hZa, ?_, ?_⟩, ⟨ha, hPa, ?_, ?_⟩⟩
      · rw [(lo_hi_of_up hz).1, prv_nxt ha]; exact (not_up_iff ha).1 hna
      · rw [(lo_hi_of_up hz).2]; linarith
      · rw [(lo_hi_of_up hu).1]; linarith
      · rw [(lo_hi_of_up hu).2]; exact (not_up_iff ha).1 hna
    · have hna : w.up a := upa.2 hu
      have hz : ¬ w.up (nxt w.C a) := fun h => upZ.1 h hna
      rw [len_of_up hna, len_of_not_up hPa hu] at hA
      rw [len_of_up hna, len_of_not_up hZa hz, prv_nxt ha] at hZ
      refine ⟨⟨hPa, hZa, ?_, ?_⟩, ⟨ha, hPa, ?_, ?_⟩⟩
      · rw [(lo_hi_of_not_up hZa hz).1]; linarith
      · rw [(lo_hi_of_not_up hZa hz).2, prv_nxt ha]; exact hna
      · rw [(lo_hi_of_not_up hPa hu).1]; exact hna
      · rw [(lo_hi_of_not_up hPa hu).2]; linarith
  refine ⟨pos.1, pos.2, fun x hx r1 r2 => ?_⟩
  have d1 : prv w.C a ≠ a := w.prv_ne ha
  have d2 : a ≠ nxt w.C a := (w.nxt_ne ha).symm
  have d3 : prv w.C a ≠ nxt w.C a := (nxt_ne_prv ha h3).symm
  rw [Row.eval_tt] at r1 r2
  -- adding the two rows
  have key : x (prv w.C a) a = x a (nxt w.C a) := by
    have e1 := hx _ hPa _ hZa d3
    have e2 := hx _ hPa _ ha d1
    rw [e2, e1] at r2
    clear e1 e2 hx
    generalize x (prv w.C a) a = u at *
    generalize x a (nxt w.C a) = v at *
    generalize x (prv w.C a) (nxt w.C a) = z at *
    revert u v z; decide
  refine ⟨key, ?_⟩
  simp only [asg]
  rw [show nxt w.C (prv w.C a) = a from nxt_prv ha, key]
  by_cases hu : w.up (prv w.C a)
  · rw [if_pos hu, if_neg (fun h => upa.1 h hu)]
    generalize x a (nxt w.C a) = u; revert u; decide
  · rw [if_neg hu, if_pos (upa.2 hu)]
    generalize x a (nxt w.C a) = u; revert u; decide

/-! ### `M - V` on sets of creases -/

lemma card_val_one (σ : w.C → ZMod 2) {S : Finset ι} (hS : S ⊆ w.C) :
    (Finset.univ.filter fun j : w.C => j.1 ∈ S ∧ σ j = 1).card =
      (S.filter fun j => w.ext0 σ j = 1).card := by
  apply Finset.card_bij (fun j _ => j.1)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, by rw [ext0_mem]; exact hj.2⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro j hj
    simp only [Finset.mem_filter] at hj
    refine ⟨⟨j, hS hj.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have e := ext0_mem σ ⟨j, hS hj.1⟩
    exact ⟨hj.1, by rw [← e]; exact hj.2⟩

lemma mvOn_eq (σ : w.C → ZMod 2) {S : Finset ι} (hS : S ⊆ w.C) :
    Chain.mvOn σ S = (S.card : ℤ) - 2 * ((S.filter fun j => w.ext0 σ j = 1).card : ℤ) := by
  unfold Chain.mvOn; rw [card_val_one σ hS]

lemma mv_eq (σ : w.C → ZMod 2) :
    w.mv σ = (w.C.card : ℤ) - 2 * ((w.C.filter fun j => w.ext0 σ j = 1).card : ℤ) := by
  rw [mv_eq_mvOn, mvOn_eq σ subset_rfl]

/-- `M - V` adds up over the run's creases and the rest, for `k` even. -/
lemma mv_split (R : w.RunData) (hk : Even R.k) (σ : w.C → ZMod 2) :
    w.mv σ = Chain.mvOn σ R.B + (w.runCrimp R).mv (Chain.restrict R σ) := by
  have hext : ∀ j, (w.runCrimp R).ext0 (Chain.restrict R σ) j =
      if j ∈ (w.runCrimp R).C then w.ext0 σ j else 0 := by
    intro j; rw [ext0_restrict, if_pos (Or.inl hk)]
  rw [mv_eq, mvOn_eq σ R.B_subset, mv_eq]
  have hf : ((w.runCrimp R).C.filter fun j => (w.runCrimp R).ext0 (Chain.restrict R σ) j = 1) =
      (w.runCrimp R).C.filter fun j => w.ext0 σ j = 1 := by
    ext j; simp only [Finset.mem_filter, hext]
    constructor
    · rintro ⟨h1, h2⟩; rw [if_pos h1] at h2; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; rw [if_pos h1]; exact ⟨h1, h2⟩
  rw [hf]
  have hU : w.C = R.B ∪ (w.runCrimp R).C := by
    rw [runCrimp_C, Finset.union_sdiff_of_subset R.B_subset]
  have hD : Disjoint R.B (w.runCrimp R).C := by
    rw [runCrimp_C]; exact Finset.disjoint_sdiff
  conv_lhs => rw [hU]
  rw [Finset.card_union_of_disjoint hD, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hD)]
  push_cast; ring

/-! ### Generic walks -/

/-- Two adjacent sectors of equal angle end on the same ray. -/
lemma c_prv_eq_c_nxt {k : ι} (hk : k ∈ w.C) (h : w.len k = w.len (nxt w.C k)) :
    w.c (prv w.C k) = w.c (nxt w.C k) := by
  have hn := w.nxt_mem hk
  have e := up_nxt hk
  by_cases hu : w.up k
  · have hn' : ¬ w.up (nxt w.C k) := fun h' => e.1 h' hu
    rw [len_of_up hu, len_of_not_up hn hn', prv_nxt hk] at h
    linarith
  · have hn' : w.up (nxt w.C k) := e.2 hu
    rw [len_of_not_up hk hu, len_of_up hn', prv_nxt hk] at h
    linarith

/-- At a generic vertex every crimped run is a single sector. -/
lemma generic_k (hg : w.Generic) (R : w.RunData) : R.k = 0 := by
  by_contra hk
  have h1 : w.len (R.t 1) = w.len (nxt w.C (R.t 1)) := by
    rw [← R.t_succ, R.hrun 1 (by omega)]; rfl
  have := c_prv_eq_c_nxt (R.t_mem 1) h1
  rw [R.prv_t_succ, ← R.t_succ] at this
  have := hg (R.t_mem 0) (R.t_mem 2) this
  have := R.t_inj (i := 0) (j := 2) (by have := R.hcard; omega) (by have := R.hcard; omega) this
  omega

lemma generic_runCrimp (hg : w.Generic) (R : w.RunData) : (w.runCrimp R).Generic :=
  fun i hi j hj h => hg (Finset.mem_sdiff.1 hi).1 (Finset.mem_sdiff.1 hj).1 h

/-- At a generic vertex the recursion ends with two creases. -/
lemma generic_allEq (hg : w.Generic) (h : w.AllEq) : w.C.card = 2 := by
  by_contra h2
  have h3 : 3 ≤ w.C.card := by have := w.two_le; omega
  obtain ⟨k, hk⟩ := w.nonempty
  have := c_prv_eq_c_nxt hk (h _ hk _ (w.nxt_mem hk))
  exact nxt_ne_prv hk h3 (hg (w.nxt_mem hk) (w.prv_mem hk) this.symm)

/-- Without taco–taco rows every crimped run is a single sector. -/
lemma noTC_k (hn : w.NoTC) (R : w.RunData) : R.k = 0 := by
  by_contra hk
  have hc := R.c_t_two (i := 0) (by omega)
  have e1 : w.up (R.t 1) ↔ ¬ w.up (R.t 0) := by rw [R.t_succ]; exact up_nxt (R.t_mem 0)
  have e2 : w.up (R.t 2) ↔ ¬ w.up (R.t 1) := by rw [R.t_succ]; exact up_nxt (R.t_mem 1)
  have hne : R.t 0 ≠ R.t 2 := fun e => by
    have := R.t_inj (i := 0) (j := 2) (by have := R.hcard; omega) (by have := R.hcard; omega) e
    omega
  exact hn _ _ ⟨R.t_mem 0, R.t_mem 2, hne, hc.symm, by tauto⟩

lemma noTC_runCrimp (hn : w.NoTC) (R : w.RunData) : (w.runCrimp R).NoTC :=
  fun q l ⟨hq, hl, hne, hc, hu⟩ => hn q l ⟨(Finset.mem_sdiff.1 hq).1, (Finset.mem_sdiff.1 hl).1,
    hne, hc, by rwa [runCrimp_up R hq, runCrimp_up R hl] at hu⟩

/-- Without taco–taco rows the recursion ends with two creases. -/
lemma noTC_allEq (hn : w.NoTC) (h : w.AllEq) : w.C.card = 2 := by
  by_contra h2
  have h3 : 3 ≤ w.C.card := by have := w.two_le; omega
  obtain ⟨k, hk⟩ := w.nonempty
  have := c_prv_eq_c_nxt hk (h _ hk _ (w.nxt_mem hk))
  have e1 := up_prv hk
  have e2 := up_nxt hk
  exact hn _ _ ⟨w.prv_mem hk, w.nxt_mem hk, (nxt_ne_prv hk h3).symm, this, by tauto⟩

/-- `M - V = ±2` on a set of two creases with `M - V ≡ 2 (mod 4)`. -/
lemma mv_two {σ : w.C → ZMod 2} (h2 : w.C.card = 2) (h : w.mv σ % 4 = 2) :
    w.mv σ = 2 ∨ w.mv σ = -2 := by
  rw [mv_eq] at h ⊢
  have := Finset.card_filter_le w.C (fun j => w.ext0 σ j = 1)
  rw [h2] at h this ⊢
  set V := (w.C.filter fun j => w.ext0 σ j = 1).card
  push_cast at h ⊢
  omega

/-- **Maekawa's rule on `W₄` at generic vertices.** -/
theorem W4_mv_generic : ∀ {w : Walk ι α} (c : Chain w), w.NoTC →
    ∀ σ ∈ c.W4, w.mv σ = 2 ∨ w.mv σ = -2 := by
  intro w c
  induction c with
  | @base w h =>
    intro hg σ hσ
    exact mv_two (noTC_allEq hg h) hσ
  | @step w R c ih =>
    intro hg σ hσ
    have hk : R.k = 0 := noTC_k hg R
    have hke : Even R.k := by rw [hk]; exact ⟨0, rfl⟩
    obtain ⟨h1, h2⟩ := hσ
    have hB := h1 hke
    rw [mvOn_eq σ R.B_subset] at hB
    have hc : R.B.card = 2 := by rw [R.card_B, if_pos hke, hk]
    have := Finset.card_filter_le R.B (fun j => w.ext0 σ j = 1)
    rw [mv_split R hke, mvOn_eq σ R.B_subset]
    rcases ih (noTC_runCrimp hg R) _ h2 with e | e <;> rw [e, hc] <;> rw [hc] at hB this <;>
      push_cast at hB ⊢ <;> omega

/-- A run of one sector is a single crimp. -/
lemma crimpOK_k0 (R : w.RunData) (hk : R.k = 0) : w.CrimpOK (R.t 1) :=
  R.crimpOK_t (i := 1) le_rfl (by omega) (R.four_le (Or.inr ⟨0, by omega⟩))

lemma B_k0 (R : w.RunData) (hk : R.k = 0) : R.B = {R.A, R.t 1} := by
  ext x
  rw [R.mem_B, if_pos ⟨0, by omega⟩]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, -, hi, rfl⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, le_rfl, by omega, rfl⟩
    · exact ⟨1, by omega, by omega, rfl⟩

lemma crimp_eq_runCrimp_k0 (R : w.RunData) (hk : R.k = 0) :
    w.crimp (R.t 1) (crimpOK_k0 R hk) = w.runCrimp R := by
  refine ext ?_ rfl
  ext x
  simp only [crimp_C, mem_crimpC, runCrimp_C, Finset.mem_sdiff, B_k0 R hk, Finset.mem_insert,
    Finset.mem_singleton, R.prv_t_succ 0]
  show x ≠ R.t 1 ∧ x ≠ R.A ∧ x ∈ w.C ↔ x ∈ w.C ∧ ¬(x = R.A ∨ x = R.t 1)
  tauto

/-- At two creases, every assignment with `M - V ≡ 2 (mod 4)` folds flat. -/
lemma base_two_flat (h2 : w.C.card = 2) {σ : w.C → ZMod 2} (hσ : w.mv σ % 4 = 2) :
    σ ∈ w.Wflat := by
  obtain ⟨k, hk⟩ := w.nonempty
  have hn := w.nxt_ne hk
  have hnC := w.nxt_mem hk
  have hpn : prv w.C k = nxt w.C k := ((two_creases h2 hnC hk).resolve_left hn).symm
  have hnn : nxt w.C (nxt w.C k) = k :=
    (two_creases h2 (w.nxt_mem hnC) hk).resolve_right
      (fun f => w.nxt_ne hnC (f.trans hpn))
  have hcase : ∀ j : w.C, j.1 = k ∨ j.1 = nxt w.C k := fun j => by
    rcases two_creases h2 j.2 hk with e | e
    · exact Or.inl e
    · exact Or.inr (e.trans hpn)
  -- `σ` takes the same value on both creases
  have hmv := mv_two h2 hσ
  have hsame : σ ⟨k, hk⟩ = σ ⟨nxt w.C k, hnC⟩ := by
    have hC : w.C = {k, nxt w.C k} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
      · rw [h2, Finset.card_pair (Ne.symm hn)]
    have hp := (mvOn_two_iff σ (S := w.C) (p := 1) (by rw [h2])).1 (by rw [← mv_eq_mvOn]; exact hσ)
    have hsum : ∑ j ∈ w.C.filter (· ∈ w.C), w.ext0 σ j =
        w.ext0 σ k + w.ext0 σ (nxt w.C k) := by
      rw [Finset.filter_true_of_mem (fun x hx => hx)]
      calc ∑ j ∈ w.C, w.ext0 σ j = ∑ j ∈ ({k, nxt w.C k} : Finset ι), w.ext0 σ j := by
            rw [← hC]
        _ = _ := Finset.sum_pair (Ne.symm hn)
    rw [hsum] at hp
    have e1 := ext0_mem σ ⟨k, hk⟩
    have e2 := ext0_mem σ ⟨nxt w.C k, hnC⟩
    simp only at e1 e2
    rw [e1, e2] at hp
    revert hp
    generalize σ ⟨k, hk⟩ = u; generalize σ ⟨nxt w.C k, hnC⟩ = v
    revert u v; decide
  have hupn : w.up (nxt w.C k) ↔ ¬ w.up k := up_nxt hk
  -- the two stackings realise the two constant assignments
  have asgv : ∀ (a b : ℤ), a ≠ b → ∀ j : w.C,
      w.asg (xOf fun i => if i = k then a else b) j =
        (if a < b then 1 else 0) + if w.up k then 0 else 1 := by
    intro a b hab j
    rw [asg_xOf]
    rcases hcase j with e | e
    · rw [e]
      show (if (if k = k then a else b) < (if nxt w.C k = k then a else b) then (1 : ZMod 2)
        else 0) + _ = _
      rw [if_pos rfl, if_neg hn]
    · rw [e, hnn]
      show (if (if nxt w.C k = k then a else b) < (if k = k then a else b) then (1 : ZMod 2)
        else 0) + _ = _
      rw [if_pos rfl, if_neg hn]
      by_cases hu : w.up k
      · rw [if_neg (fun h => hupn.1 h hu), if_pos hu]
        rcases lt_or_gt_of_ne hab with h | h
        · rw [if_neg (not_lt.2 h.le), if_pos h]; decide
        · rw [if_pos h, if_neg (not_lt.2 h.le)]; decide
      · rw [if_pos (hupn.2 hu), if_neg hu]
        rcases lt_or_gt_of_ne hab with h | h
        · rw [if_neg (not_lt.2 h.le), if_pos h]; decide
        · rw [if_pos h, if_neg (not_lt.2 h.le)]; decide
  by_cases hv : σ ⟨k, hk⟩ = 1 + if w.up k then 0 else 1
  · refine ⟨_, flat_two h2 hk 0 1 (by norm_num), funext fun j => ?_⟩
    rw [asgv 0 1 (by norm_num) j, if_pos (by norm_num)]
    rcases hcase j with e | e
    · rw [show j = ⟨k, hk⟩ from Subtype.ext e, hv]
    · rw [show j = ⟨nxt w.C k, hnC⟩ from Subtype.ext e, ← hsame, hv]
  · refine ⟨_, flat_two h2 hk 1 0 (by norm_num), funext fun j => ?_⟩
    rw [asgv 1 0 (by norm_num) j, if_neg (by norm_num), zero_add]
    have : σ ⟨k, hk⟩ = if w.up k then 0 else 1 := by
      revert hv; generalize σ ⟨k, hk⟩ = u
      generalize (if w.up k then (0 : ZMod 2) else 1) = v; revert u v; decide
    rcases hcase j with e | e
    · rw [show j = ⟨k, hk⟩ from Subtype.ext e, this]
    · rw [show j = ⟨nxt w.C k, hnC⟩ from Subtype.ext e, ← hsame, this]

/-- A crimp of a single sector lifts `W₄ ⊆ W_flat` from the crimped walk. -/
lemma step_k0_flat (R : w.RunData) (hk : R.k = 0) (c : Chain (w.runCrimp R))
    (ih : c.W4 ⊆ (w.runCrimp R).Wflat) : (Chain.step R c).W4 ⊆ w.Wflat := by
  intro σ hσ
  have hke : Even R.k := ⟨0, by omega⟩
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h', hf', he'⟩ := ih h2
  have hc := crimpOK_k0 R hk
  have e := crimp_eq_runCrimp_k0 R hk
  have hf'' : (w.crimp _ hc).IsFlat h' := by rw [e]; exact hf'
  have hA : R.A ∈ w.C := R.hA
  have hpa : prv w.C (R.t 1) = R.A := R.prv_t_succ 0
  -- the run's two creases receive opposite assignments
  have hopp : σ ⟨R.t 1, R.t_mem 1⟩ = σ ⟨R.A, hA⟩ + 1 := by
    have hne : R.A ≠ R.t 1 := by rw [← hpa]; exact hc.A_ne_a
    have hp := (mvOn_even_iff σ R.B_subset (p := 1) (by rw [R.card_B, if_pos hke, hk])).1 (h1 hke)
    rw [show w.C.filter (· ∈ R.B) = {R.A, R.t 1} by
      rw [B_k0 R hk]; ext x; simp only [Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl)
        · exact ⟨hA, Or.inl rfl⟩
        · exact ⟨R.t_mem 1, Or.inr rfl⟩, Finset.sum_pair hne] at hp
    have e1 := ext0_mem σ ⟨R.A, hA⟩
    have e2 := ext0_mem σ ⟨R.t 1, R.t_mem 1⟩
    simp only at e1 e2
    rw [e1, e2] at hp
    revert hp
    generalize σ ⟨R.A, hA⟩ = u; generalize σ ⟨R.t 1, R.t_mem 1⟩ = v
    revert u v; decide
  set tb : Bool := decide (σ ⟨R.A, hA⟩ + (if w.up R.A then 0 else 1) = 1)
  obtain ⟨h, hf, hag, hv1, hv2⟩ := hc.exists_lift hf'' tb
  rw [hpa] at hv1
  refine ⟨h, hf, funext fun j => ?_⟩
  rw [asg_xOf]
  by_cases hj : j.1 ∈ (w.runCrimp R).C
  · have hj' : j.1 ∈ (w.crimp _ hc).C := by rw [e]; exact hj
    rw [hag j.1 hj', e]
    have := congrFun he' ⟨j.1, hj⟩
    simp only [Chain.restrict, Or.inl hke, if_true] at this
    rw [← this, asg_xOf]
    simp only [runCrimp_up R hj]
  · have hjB : j.1 ∈ R.B := by
      by_contra hb; exact hj (Finset.mem_sdiff.2 ⟨j.2, hb⟩)
    rw [B_k0 R hk, Finset.mem_insert, Finset.mem_singleton] at hjB
    have hupA : w.up (R.t 1) ↔ ¬ w.up R.A := by rw [R.t_succ]; exact up_nxt hA
    rcases hjB with e1 | e1
    · rw [show j = ⟨R.A, hA⟩ from Subtype.ext e1]
      show xOf h R.A (nxt w.C R.A) + _ = _
      rw [show nxt w.C R.A = R.t 1 from (R.t_succ 0).symm, hv1]
      by_cases hu : w.up R.A <;> simp only [hu, if_true, if_false, tb] <;>
        generalize σ ⟨R.A, hA⟩ = u <;> revert u <;> decide
    · rw [show j = ⟨R.t 1, R.t_mem 1⟩ from Subtype.ext e1, hopp]
      show xOf h (R.t 1) (nxt w.C (R.t 1)) + _ = _
      rw [hv2]
      by_cases hu : w.up R.A
      · have hut : ¬ w.up (R.t 1) := fun h => hupA.1 h hu
        simp only [if_neg hut, tb, hu, if_true]
        generalize σ ⟨R.A, hA⟩ = u; revert u; decide
      · have hut : w.up (R.t 1) := hupA.2 hu
        simp only [if_pos hut, tb, hu, if_false]
        generalize σ ⟨R.A, hA⟩ = u; revert u; decide

/-- `W₄ ⊆ W_flat` at generic vertices: Hull's recursion read modulo four is exact there. -/
theorem W4_flat_generic : ∀ {w : Walk ι α} (c : Chain w), w.NoTC → c.W4 ⊆ w.Wflat := by
  intro w c
  induction c with
  | @base w h => exact fun hg σ hσ => base_two_flat (noTC_allEq hg h) hσ
  | @step w R c ih => exact fun hg => step_k0_flat R (noTC_k hg R) c (ih (noTC_runCrimp hg R))

lemma E_generic : ∀ {w : Walk ι α} (c : Chain w), w.NoTC → 2 * (c.E + 1) = w.C.card := by
  intro w c
  induction c with
  | @base w h => intro hg; rw [noTC_allEq hg h]; rfl
  | @step w R c ih =>
    intro hg
    have hk : R.k = 0 := noTC_k hg R
    have := ih (noTC_runCrimp hg R)
    rw [runCrimp_C, Finset.card_sdiff_of_subset R.B_subset, R.card_B, if_pos ⟨0, by omega⟩,
      hk] at this
    have h4 := R.four_le (Or.inr ⟨0, by omega⟩)
    simp only [Chain.E, if_pos (show Even R.k from ⟨0, by omega⟩)]
    omega

/-- At a generic vertex every block of the recursion has two creases. -/
lemma blocks_two : ∀ {w : Walk ι α} (c : Chain w), w.NoTC →
    ∀ i ∈ w.C, (w.C.filter (labRel c i)).card = 2 := by
  intro w c
  induction c with
  | @base w h =>
    intro hg i _
    rw [show w.C.filter (labRel (Chain.base h) i) = w.C by
      ext j; simp [labRel, Chain.lab]]
    exact noTC_allEq hg h
  | @step w R c ih =>
    intro hg i hi
    have hk : R.k = 0 := noTC_k hg R
    have hke : Even R.k := ⟨0, by omega⟩
    rw [filter_lab_even R c hke hi]
    split_ifs with hiB
    · rw [R.card_B, if_pos hke, hk]
    · exact ih (noTC_runCrimp hg R) i (R.mem_C'.2 ⟨hi, hiB⟩)

/-- At a generic vertex exactly one block is forced equal by `W₄`, the others opposite. -/
lemma equal_pair : ∀ {w : Walk ι α} (c : Chain w), w.NoTC →
    ∃ i₀ ∈ w.C, ∃ j₀ ∈ w.C, i₀ ≠ j₀ ∧ c.lab i₀ = c.lab j₀ ∧
      (∀ σ ∈ c.W4, w.ext0 σ i₀ = w.ext0 σ j₀) ∧
      ∀ i ∈ w.C, ∀ j ∈ w.C, i ≠ j → c.lab i = c.lab j → c.lab i ≠ c.lab i₀ →
        ∀ σ ∈ c.W4, w.ext0 σ i ≠ w.ext0 σ j := by
  intro w c
  induction c with
  | @base w h =>
    intro hg
    have h2 := noTC_allEq hg h
    obtain ⟨k, hk⟩ := w.nonempty
    have hn := w.nxt_ne hk
    have hnC := w.nxt_mem hk
    refine ⟨k, hk, nxt w.C k, hnC, Ne.symm hn, rfl, fun σ hσ => ?_, fun i _ j _ _ _ h => absurd rfl h⟩
    have hC : w.C = {k, nxt w.C k} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
      · rw [h2, Finset.card_pair (Ne.symm hn)]
    have hp := (mvOn_two_iff σ (S := w.C) (p := 1) (by rw [h2])).1 (by rw [← mv_eq_mvOn]; exact hσ)
    have hsum : ∑ j ∈ w.C.filter (· ∈ w.C), w.ext0 σ j = w.ext0 σ k + w.ext0 σ (nxt w.C k) := by
      rw [Finset.filter_true_of_mem (fun x hx => hx)]
      calc ∑ j ∈ w.C, w.ext0 σ j = ∑ j ∈ ({k, nxt w.C k} : Finset ι), w.ext0 σ j := by
            rw [← hC]
        _ = _ := Finset.sum_pair (Ne.symm hn)
    rw [hsum] at hp
    revert hp
    generalize w.ext0 σ k = u; generalize w.ext0 σ (nxt w.C k) = v
    revert u v; decide
  | @step w R c ih =>
    intro hg
    have hk : R.k = 0 := noTC_k hg R
    have hke : Even R.k := ⟨0, by omega⟩
    have hA := A_not_C' R hke
    obtain ⟨i₀, hi₀, j₀, hj₀, hne, hlab, heq, hopp⟩ := ih (noTC_runCrimp hg R)
    have hsub : (w.runCrimp R).C ⊆ w.C := Finset.sdiff_subset
    have notB : ∀ {x}, x ∈ (w.runCrimp R).C → x ∉ R.B := fun h => (Finset.mem_sdiff.1 h).2
    have labx : ∀ {x}, x ∈ (w.runCrimp R).C → (Chain.step R c).lab x = c.lab x := by
      intro x hx; simp only [Chain.lab, if_neg (notB hx)]
    have ext_r : ∀ σ : w.C → ZMod 2, ∀ x ∈ (w.runCrimp R).C,
        (w.runCrimp R).ext0 (Chain.restrict R σ) x = w.ext0 σ x := by
      intro σ x hx; rw [ext0_restrict, if_pos hx, if_pos (Or.inl hke)]
    refine ⟨i₀, hsub hi₀, j₀, hsub hj₀, hne, by rw [labx hi₀, labx hj₀, hlab], ?_, ?_⟩
    · rintro σ ⟨-, h2⟩
      rw [← ext_r σ i₀ hi₀, ← ext_r σ j₀ hj₀]; exact heq _ h2
    · intro i hi j hj hij hl hl₀ σ hσ
      obtain ⟨h1, h2⟩ := hσ
      by_cases hiB : i ∈ R.B
      · -- the run's two creases: opposite
        have hjB : j ∈ R.B := by
          by_contra hjB
          simp only [Chain.lab, if_pos hiB, if_pos hke, if_neg hjB] at hl
          exact hA (hl ▸ c.lab_mem (R.mem_C'.2 ⟨hj, hjB⟩))
        rw [B_k0 R hk, Finset.mem_insert, Finset.mem_singleton] at hiB hjB
        have hp := (mvOn_even_iff σ R.B_subset (p := 1) (by rw [R.card_B, if_pos hke, hk])).1
          (h1 hke)
        have hne' : R.A ≠ R.t 1 := by
          intro e; have := R.t_inj (i := 0) (j := 1) (by have := R.hcard; omega)
            (by have := R.hcard; omega) e
          omega
        rw [show w.C.filter (· ∈ R.B) = {R.A, R.t 1} by
          rw [B_k0 R hk]; ext x; simp only [Finset.mem_filter, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro (rfl | rfl)
            · exact ⟨R.hA, Or.inl rfl⟩
            · exact ⟨R.t_mem 1, Or.inr rfl⟩, Finset.sum_pair hne'] at hp
        have key : w.ext0 σ R.A ≠ w.ext0 σ (R.t 1) := by
          revert hp; generalize w.ext0 σ R.A = u; generalize w.ext0 σ (R.t 1) = v
          revert u v; decide
        rcases hiB with rfl | rfl <;> rcases hjB with rfl | rfl
        · exact absurd rfl hij
        · exact key
        · exact Ne.symm key
        · exact absurd rfl hij
      · have hjB : j ∉ R.B := by
          intro hjB
          simp only [Chain.lab, if_neg hiB, if_pos hjB, if_pos hke] at hl
          exact hA (hl.symm ▸ c.lab_mem (R.mem_C'.2 ⟨hi, hiB⟩))
        have hi' := R.mem_C'.2 ⟨hi, hiB⟩
        have hj' := R.mem_C'.2 ⟨hj, hjB⟩
        rw [labx hi', labx hj'] at hl
        rw [labx hi', labx (hsub hi₀ |> fun _ => hi₀)] at hl₀
        rw [← ext_r σ i hi', ← ext_r σ j hj']
        exact hopp i hi' j hj' hij hl hl₀ _ h2

/-- **Theorem 2, second proof** (through Theorem 4 and Hull's recursion, `W₄`): the same
statement as `theorem2`. -/
theorem theorem2_hull (hg : w.NoTC) :
    (∀ i ∈ w.C, (w.C.filter (w.SameComp i)).card = 2) ∧
    (∀ i ∈ w.C, ∀ j ∈ w.C, w.SameComp i j → ∀ σ ∈ w.Wlin, ∀ τ ∈ w.Wlin,
      w.ext0 σ i + w.ext0 σ j = w.ext0 τ i + w.ext0 τ j) ∧
    (∃ i₀ ∈ w.C, ∃ j₀ ∈ w.C, i₀ ≠ j₀ ∧ w.SameComp i₀ j₀ ∧
      (∀ σ ∈ w.Wlin, w.ext0 σ i₀ = w.ext0 σ j₀) ∧
      ∀ i ∈ w.C, ∀ j ∈ w.C, i ≠ j → w.SameComp i j → ¬ w.SameComp i i₀ →
        ∀ σ ∈ w.Wlin, w.ext0 σ i ≠ w.ext0 σ j) ∧
    (∀ σ ∈ w.Wlin, w.mv σ = 2 ∨ w.mv σ = -2) := by
  obtain ⟨c⟩ := exists_chain _ w rfl
  obtain ⟨-, -, hcomp⟩ := card_Wlin c
  have hW := (theorem3 c).1
  have hf : ∀ i ∈ w.C, w.C.filter (w.SameComp i) = w.C.filter (labRel c i) := by
    intro i hi; ext j
    simp only [Finset.mem_filter, labRel]
    exact ⟨fun ⟨hj, h⟩ => ⟨hj, (hcomp i hi j hj).1 h⟩, fun ⟨hj, h⟩ => ⟨hj, (hcomp i hi j hj).2 h⟩⟩
  refine ⟨fun i hi => by rw [hf i hi]; exact blocks_two c hg i hi, ?_, ?_, ?_⟩
  · intro i hi j hj hij σ hσ τ hτ
    have hp := (lemma4 hτ).1
    have hσ' : σ ∈ w.Part w.SameComp τ := hp ▸ hσ
    have := hσ' i hi
    unfold bsum at this
    by_cases hij' : i = j
    · subst hij'; rw [zmod2_add_self, zmod2_add_self]
    · have hcl : w.C.filter (w.SameComp i) = {i, j} := by
        symm; apply Finset.eq_of_subset_of_card_le
        · intro x hx; simp at hx; rcases hx with rfl | rfl
          · exact Finset.mem_filter.2 ⟨hi, conn_refl _⟩
          · exact Finset.mem_filter.2 ⟨hj, hij⟩
        · rw [hf i hi, blocks_two c hg i hi, Finset.card_pair hij']
      rw [hcl, Finset.sum_pair hij', Finset.sum_pair hij'] at this
      exact this
  · obtain ⟨i₀, hi₀, j₀, hj₀, hne, hlab, heq, hopp⟩ := equal_pair c hg
    refine ⟨i₀, hi₀, j₀, hj₀, hne, (hcomp i₀ hi₀ j₀ hj₀).2 hlab, fun σ hσ => heq σ (hW ▸ hσ),
      fun i hi j hj hij h1 h2 σ hσ => hopp i hi j hj hij ((hcomp i hi j hj).1 h1)
        (fun e => h2 ((hcomp i hi i₀ hi₀).2 e)) σ (hW ▸ hσ)⟩
  · intro σ hσ; exact W4_mv_generic c hg σ (hW ▸ hσ)

/-! ### Theorem 2 by the gauge -/

/-- With two creases, the two creases are the successors of each other. -/
lemma nxt_of_two (h2 : w.C.card = 2) {i j : ι} (hi : i ∈ w.C) (hj : j ∈ w.C) (hij : i ≠ j) :
    nxt w.C i = j := by
  have e1 : j = prv w.C i := (two_creases h2 hj hi).resolve_left (Ne.symm hij)
  have e2 : nxt w.C i = prv w.C i :=
    (two_creases h2 (w.nxt_mem hi) hi).resolve_left (w.nxt_ne hi)
  rw [e2, ← e1]

/-- With two creases, every solution gives the two creases equal assignments. -/
lemma asg_eq_of_two (h2 : w.C.card = 2) {x : ι → ι → ZMod 2} (hx : w.Antisymm x) {i j : ι}
    (hi : i ∈ w.C) (hj : j ∈ w.C) : w.ext0 (w.asg x) i = w.ext0 (w.asg x) j := by
  by_cases hij : i = j
  · rw [hij]
  rw [ext0_asg x hi, ext0_asg x hj, nxt_of_two h2 hi hj hij,
    nxt_of_two h2 hj hi (Ne.symm hij), hx i hi j hj hij]
  have hu := up_nxt hi
  rw [nxt_of_two h2 hi hj hij] at hu
  generalize x i j = a
  by_cases h : w.up i
  · rw [if_pos h, if_neg (fun h' => hu.1 h' h)]
    revert a; decide
  · rw [if_neg h, if_pos (hu.2 h)]
    revert a; decide

/-- Theorem 2 at a walk with two creases: there is no row, and the two creases form the one
pair, forced equal. -/
theorem theorem2_two (h2 : w.C.card = 2) :
    (∀ i ∈ w.C, (w.C.filter (w.SameComp i)).card = 2) ∧
    (∀ i ∈ w.C, ∀ j ∈ w.C, w.SameComp i j → ∀ σ ∈ w.Wlin, ∀ τ ∈ w.Wlin,
      w.ext0 σ i + w.ext0 σ j = w.ext0 τ i + w.ext0 τ j) ∧
    (∃ i₀ ∈ w.C, ∃ j₀ ∈ w.C, i₀ ≠ j₀ ∧ w.SameComp i₀ j₀ ∧
      (∀ σ ∈ w.Wlin, w.ext0 σ i₀ = w.ext0 σ j₀) ∧
      ∀ i ∈ w.C, ∀ j ∈ w.C, i ≠ j → w.SameComp i j → ¬ w.SameComp i i₀ →
        ∀ σ ∈ w.Wlin, w.ext0 σ i ≠ w.ext0 σ j) ∧
    (∀ σ ∈ w.Wlin, w.mv σ = 2 ∨ w.mv σ = -2) := by
  -- all adjacent pairs coincide, so all creases are in one component
  have hsc : ∀ i ∈ w.C, ∀ j ∈ w.C, w.SameComp i j := by
    intro i hi j hj
    by_cases hij : i = j
    · rw [hij]; exact conn_refl _
    unfold SameComp adj
    rw [nxt_of_two h2 hi hj hij, nxt_of_two h2 hj hi (Ne.symm hij), Sym2.eq_swap]
    exact conn_refl _
  have hall : ∀ i ∈ w.C, w.C.filter (w.SameComp i) = w.C := fun i hi =>
    Finset.filter_true_of_mem fun j hj => hsc i hi j hj
  obtain ⟨k, hk⟩ := w.nonempty
  have hk' := w.nxt_mem hk
  refine ⟨fun i hi => by rw [hall i hi, h2], ?_, ⟨k, hk, nxt w.C k, hk', (w.nxt_ne hk).symm,
    hsc k hk _ hk', ?_, fun i hi j hj _ _ h => absurd (hsc i hi k hk) h⟩, ?_⟩
  · rintro i hi j hj - _ ⟨x, hx, -, rfl⟩ _ ⟨y, hy, -, rfl⟩
    rw [asg_eq_of_two h2 hx hi hj, asg_eq_of_two h2 hy hi hj, zmod2_add_self, zmod2_add_self]
  · rintro _ ⟨x, hx, -, rfl⟩
    exact asg_eq_of_two h2 hx hk hk'
  · rintro _ ⟨x, hx, hs, rfl⟩
    exact mv_two h2 (mv_mod_four hx hs)

/-- **Theorem 2 (pairing at a generic vertex).**  The taco–tortilla rows pair the creases: each
component of `H_v` containing an adjacent pair contains exactly two; every solution satisfies
one relation per pair (equal or opposite assignments); exactly one pair is forced equal, all
the others opposite; hence every solution of the rows has `M - V = ±2`, transitive or not.
Proof: the gauge of a lowest crease and the sides cut by the extreme creases (`pairing`); the
pair forced equal is formed by a highest and a lowest crease. -/
theorem theorem2 (hg : w.NoTC) :
    (∀ i ∈ w.C, (w.C.filter (w.SameComp i)).card = 2) ∧
    (∀ i ∈ w.C, ∀ j ∈ w.C, w.SameComp i j → ∀ σ ∈ w.Wlin, ∀ τ ∈ w.Wlin,
      w.ext0 σ i + w.ext0 σ j = w.ext0 τ i + w.ext0 τ j) ∧
    (∃ i₀ ∈ w.C, ∃ j₀ ∈ w.C, i₀ ≠ j₀ ∧ w.SameComp i₀ j₀ ∧
      (∀ σ ∈ w.Wlin, w.ext0 σ i₀ = w.ext0 σ j₀) ∧
      ∀ i ∈ w.C, ∀ j ∈ w.C, i ≠ j → w.SameComp i j → ¬ w.SameComp i i₀ →
        ∀ σ ∈ w.Wlin, w.ext0 σ i ≠ w.ext0 σ j) ∧
    (∀ σ ∈ w.Wlin, w.mv σ = 2 ∨ w.mv σ = -2) := by
  by_cases h2 : w.C.card = 2
  · exact theorem2_two h2
  have h3 : 3 ≤ w.C.card := by have := w.two_le; omega
  obtain ⟨B, hB, hmin⟩ := w.C.exists_min_image w.c w.nonempty
  obtain ⟨T, hT, hmax⟩ := w.C.exists_max_image w.c w.nonempty
  obtain ⟨hcard, htop, -, hsol⟩ := pairing hg h3 hB hT hmin hmax
  have hTB : w.SameComp T B := by
    have : B ∈ w.C.filter (w.SameComp T) := by rw [htop]; simp
    exact (Finset.mem_filter.1 this).2
  refine ⟨hcard, ?_, ⟨T, hT, B, hB, top_ne_bot hT hmax hmin, hTB, ?_, ?_⟩, ?_⟩
  · rintro i hi j hj hij _ ⟨x, hx, hs, rfl⟩ _ ⟨y, hy, hs', rfl⟩
    have e1 := asg_add_asg hg hB hmin hx hs hi hj hij
    have e2 := asg_add_asg hg hB hmin hy hs' hi hj hij
    rw [ext0_asg x hi, ext0_asg x hj, ext0_asg y hi, ext0_asg y hj]
    exact e1.trans e2.symm
  · rintro _ ⟨x, hx, hs, rfl⟩
    rw [ext0_asg x hT, ext0_asg x hB]
    exact (hsol x hx hs).1
  · rintro i hi j hj hij h1 h2' _ ⟨x, hx, hs, rfl⟩
    rw [ext0_asg x hi, ext0_asg x hj]
    exact (hsol x hx hs).2.1 i hi j hj hij h1 h2'
  · rintro _ ⟨x, hx, hs, rfl⟩
    rw [(hsol x hx hs).2.2]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **Theorem 2, second statement.**  At a generic vertex, every assignment of the layer
variables that satisfies the taco–tortilla rows has `M - V = ±2`. -/
theorem maekawa_generic (hg : w.NoTC) {x : ι → ι → ZMod 2} (hx : w.Antisymm x)
    (hs : ∀ r ∈ w.ttRows, r.eval x = 0) : w.mv (w.asg x) = 2 ∨ w.mv (w.asg x) = -2 := by
  have hsol : w.IsSol x := fun r hr => by
    rcases mem_rows.1 hr with h | h
    · exact hs r h
    · rw [tcRows_eq_empty_of_noTC hg] at h; simp at h
  exact (theorem2 hg).2.2.2 _ ⟨x, hx, hsol, rfl⟩

/-- **Corollary 1.**  At a generic vertex of degree `2m`, the flat-foldable assignments are
exactly the assignments induced by the solutions of the taco–tortilla rows, exactly those
satisfying the `m` relations of Theorem 2, and there are `2^m` of them. -/
theorem corollary1 (hg : w.NoTC) {σ₀ : w.C → ZMod 2} (h₀ : σ₀ ∈ w.Wflat) :
    w.Wflat = w.Wlin ∧ w.Wlin = w.Part w.SameComp σ₀ ∧ 2 * w.gamma = w.C.card ∧
      w.Wflat.ncard = 2 ^ w.gamma := by
  obtain ⟨c⟩ := exists_chain _ w rfl
  obtain ⟨hcard, hgam, -⟩ := card_Wlin c
  have hE := E_generic c hg
  have hWf : w.Wflat = w.Wlin :=
    subset_antisymm Wflat_subset_Wlin ((theorem3 c).1 ▸ W4_flat_generic c hg)
  refine ⟨hWf, (lemma4 (Wflat_subset_Wlin h₀)).1, by rw [hgam]; exact hE, ?_⟩
  rw [hWf, hcard, hgam]; congr 1; omega

/-- In a crimp of a single sector, `W₄` forces opposite assignments on its two creases. -/
lemma opp_k0 (R : w.RunData) (hk : R.k = 0) {c : Chain (w.runCrimp R)} {σ : w.C → ZMod 2}
    (hσ : σ ∈ (Chain.step R c).W4) : w.ext0 σ R.A ≠ w.ext0 σ (R.t 1) := by
  have hke : Even R.k := ⟨0, by omega⟩
  have hp := (mvOn_even_iff σ R.B_subset (p := 1) (by rw [R.card_B, if_pos hke, hk])).1 (hσ.1 hke)
  have hne' : R.A ≠ R.t 1 := by
    intro e; have := R.t_inj (i := 0) (j := 1) (by have := R.hcard; omega)
      (by have := R.hcard; omega) e
    omega
  rw [show w.C.filter (· ∈ R.B) = {R.A, R.t 1} by
    rw [B_k0 R hk]; ext x; simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨R.hA, Or.inl rfl⟩
      · exact ⟨R.t_mem 1, Or.inr rfl⟩, Finset.sum_pair hne'] at hp
  revert hp; generalize w.ext0 σ R.A = u; generalize w.ext0 σ (R.t 1) = v
  revert u v; decide

/-- At a vertex without taco–taco rows (in particular at a generic vertex), a sector of
smallest angle is strictly smaller than its neighbours: two equal consecutive angles would put
two creases of the same type on one ray. -/
lemma strict_of_noTC (hn : w.NoTC) {a : ι} (ha : a ∈ w.C) (h3 : 3 ≤ w.C.card)
    (hmin : ∀ g ∈ w.C, w.len a ≤ w.len g) :
    w.len a < w.len (prv w.C a) ∧ w.len a < w.len (nxt w.C a) := by
  have hPa := w.prv_mem ha
  refine ⟨lt_of_le_of_ne (hmin _ hPa) fun h => ?_, lt_of_le_of_ne (hmin _ (w.nxt_mem ha)) fun h => ?_⟩
  · have e := c_prv_eq_c_nxt hPa (by rw [nxt_prv ha]; exact h.symm)
    rw [nxt_prv ha] at e
    have hne : prv w.C (prv w.C a) ≠ a := fun h1 => by
      have h2 := congrArg (nxt w.C) h1
      rw [nxt_prv hPa] at h2
      exact nxt_ne_prv ha h3 h2.symm
    exact hn _ _ ⟨w.prv_mem hPa, ha, hne, e, by rw [up_prv hPa, up_prv ha, not_not]⟩
  · have e := c_prv_eq_c_nxt ha h
    exact hn _ _ ⟨hPa, w.nxt_mem ha, (nxt_ne_prv ha h3).symm, e, by rw [up_prv ha, up_nxt ha]⟩

/-- At a generic vertex, a sector of smallest angle is strictly smaller than its neighbours. -/
lemma strict_of_generic (hg : w.Generic) {a : ι} (ha : a ∈ w.C) (h3 : 3 ≤ w.C.card)
    (hmin : ∀ g ∈ w.C, w.len a ≤ w.len g) :
    w.len a < w.len (prv w.C a) ∧ w.len a < w.len (nxt w.C a) :=
  strict_of_noTC (generic_noTC hg) ha h3 hmin

/-- The run formed by a sector of smallest angle at a vertex without taco–taco rows. -/
def runOfMin (hg : w.NoTC) {a : ι} (ha : a ∈ w.C) (h4 : 4 ≤ w.C.card)
    (hmin : ∀ g ∈ w.C, w.len a ≤ w.len g) : w.RunData where
  A := prv w.C a
  k := 0
  hA := w.prv_mem ha
  hcard := by omega
  hmin := fun g hg' => by rw [nxt_prv ha]; exact hmin g hg'
  hrun := fun i hi => by
    rw [show i = 0 by omega]; rfl
  hbigA := by rw [nxt_prv ha]; exact (strict_of_noTC hg ha (by omega) hmin).1
  hbigZ := by
    show w.len (nxt w.C (prv w.C a)) < w.len (nxt w.C (nxt w.C (prv w.C a)))
    rw [nxt_prv ha]; exact (strict_of_noTC hg ha (by omega) hmin).2

/-- **Lemma 6 (crimping a sector).**  Let `f_a` be a sector of smallest angle at a vertex
without taco–taco rows (in the paper: at a generic vertex), and `w'` the walk obtained by
crimping it.
(a) the big–little–big rows form a component of `H_v` whose only adjacent pairs are those of
    `e_{a-1}` and `e_a`, and it forces opposite assignments on them;
(b) on the other creases, the components of `H_v` and of `H_{w'}` pair the same creases, and
    force the same relations. -/
theorem lemma5 (hg : w.NoTC) {a : ι} (ha : a ∈ w.C) (h4 : 4 ≤ w.C.card)
    (hmin : ∀ g ∈ w.C, w.len a ≤ w.len g) :
    let w' := w.runCrimp (runOfMin hg ha h4 hmin)
    (w.SameComp (prv w.C a) a ∧ (∀ j ∈ w.C, w.SameComp (prv w.C a) j → j = prv w.C a ∨ j = a) ∧
      ∀ σ ∈ w.Wlin, w.ext0 σ (prv w.C a) ≠ w.ext0 σ a) ∧
    w'.C = (w.C.erase (prv w.C a)).erase a ∧
    (∀ i ∈ w'.C, ∀ j ∈ w'.C, w.SameComp i j ↔ w'.SameComp i j) ∧
    (∀ σ ∈ w.Wlin, ∀ σ' ∈ w'.Wlin, ∀ i ∈ w'.C, ∀ j ∈ w'.C, w'.SameComp i j →
      w.ext0 σ i + w.ext0 σ j = w'.ext0 σ' i + w'.ext0 σ' j) := by
  intro w'
  set R := runOfMin hg ha h4 hmin
  have hk : R.k = 0 := rfl
  have hke : Even R.k := ⟨0, rfl⟩
  have hA : R.A = prv w.C a := rfl
  have ht1 : R.t 1 = a := by show nxt w.C (prv w.C a) = a; exact nxt_prv ha
  obtain ⟨c'⟩ := exists_chain _ (w.runCrimp R) rfl
  set c := Chain.step R c'
  obtain ⟨-, -, hcomp⟩ := card_Wlin c
  obtain ⟨-, -, hcomp'⟩ := card_Wlin c'
  have hW := (theorem3 c).1
  have hW' := (theorem3 c').1
  have hAn := A_not_C' R hke
  have hB : R.B = {prv w.C a, a} := by rw [B_k0 R hk, hA, ht1]
  have hsub : (w.runCrimp R).C ⊆ w.C := Finset.sdiff_subset
  have labx : ∀ {x}, x ∈ (w.runCrimp R).C → c.lab x = c'.lab x := by
    intro x hx; simp only [c, Chain.lab, if_neg (Finset.mem_sdiff.1 hx).2]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hcomp _ (w.prv_mem ha) _ ha]
    simp only [c, Chain.lab, hB, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
      if_true]
  · intro j hj h
    rw [hcomp _ (w.prv_mem ha) _ hj] at h
    by_contra hjB
    have hjB' : j ∉ R.B := by rw [hB]; simpa using hjB
    simp only [c, Chain.lab, hB, Finset.mem_insert, Finset.mem_singleton, true_or, if_true,
      if_pos hke] at h
    rw [if_neg hjB] at h
    exact hAn (h ▸ c'.lab_mem (R.mem_C'.2 ⟨hj, hjB'⟩))
  · intro σ hσ
    have := opp_k0 R hk (c := c') (hW ▸ hσ)
    rwa [hA, ht1] at this
  · show w.C \ R.B = _
    rw [hB]; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase]; tauto
  · intro i hi j hj
    rw [hcomp i (hsub hi) j (hsub hj), hcomp' i hi j hj, labx hi, labx hj]
  · intro σ hσ σ' hσ' i hi j hj hij
    have hr : Chain.restrict R σ ∈ (w.runCrimp R).Wlin := hW' ▸ (hW ▸ hσ).2
    have := (theorem2 (noTC_runCrimp hg R)).2.1 i hi j hj hij _ hr σ' hσ'
    rwa [ext0_restrict, ext0_restrict, if_pos hi, if_pos hj, if_pos (Or.inl hke),
      if_pos (Or.inl hke)] at this

end Walk

end Origami
