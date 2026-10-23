import Origami.Perturb

/-!
# Examples 1, 3 and 4 of the paper

The vertices of the examples are concrete walks indexed by `Fin n`, with positions in degrees
(Eq. (4)): the crease `e_k` of the paper is `k - 1`, and the sector `f_k`, which ends at
`e_k`, is `k - 1` as well.  Their rows, flat-folded states and explicit solutions are checked
by `decide`, in the kernel.  The sets `W_lin` and `W_flat` are then determined with the general
theorems:

* `W_lin` from above by Corollary 3(a) (every solution has `M - V ≡ 2 (mod 4)`, and `±2` at
  degree four) or Theorem 4, from below by explicit solutions;
* `W_flat` from above by Corollary 3(b) (Maekawa) and by an exhaustive check of the stackings,
  from below by explicit flat-folded states.

A stacking of `n` sectors given by integer heights has the layer variables of the permutation
of its ranks (`xOf_rank`), so a statement about all flat-folded states of a vertex of `Fin n`
reduces to a finite check over the functions `Fin n → Fin n`.
-/

set_option linter.unusedSectionVars false

namespace Origami

/-! ### Stackings are permutations -/

/-- The rank of `i` among the heights `h`. -/
def rankOf {n : ℕ} (h : Fin n → ℤ) (i : Fin n) : Fin n :=
  ⟨(Finset.univ.filter fun j => h j < h i).card, by
    have := Finset.card_lt_card
      (Finset.filter_ssubset.2 ⟨i, Finset.mem_univ i, lt_irrefl (h i)⟩ :
        (Finset.univ.filter fun j => h j < h i) ⊂ Finset.univ)
    rwa [Finset.card_univ, Fintype.card_fin] at this⟩

lemma rankOf_lt_iff {n : ℕ} {h : Fin n → ℤ} (hinj : Function.Injective h) (i j : Fin n) :
    rankOf h i < rankOf h j ↔ h i < h j := by
  have key : ∀ a b, h a < h b → rankOf h a < rankOf h b := by
    intro a b hab
    rw [Fin.lt_def]
    show (Finset.univ.filter fun j => h j < h a).card < (Finset.univ.filter fun j => h j < h b).card
    apply Finset.card_lt_card
    refine ⟨fun x hx => ?_, fun hs => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx.trans hab
    · have ha : a ∈ Finset.univ.filter fun j => h j < h b := by simp [hab]
      have := hs ha
      simp at this
  refine ⟨fun hr => ?_, key i j⟩
  rcases lt_trichotomy (h i) (h j) with e | e | e
  · exact e
  · rw [hinj e] at hr; exact absurd hr (lt_irrefl _)
  · exact absurd (key _ _ e) (not_lt.2 hr.le)

lemma rankOf_injective {n : ℕ} {h : Fin n → ℤ} (hinj : Function.Injective h) :
    Function.Injective (rankOf h) := by
  intro i j e
  by_contra hne
  rcases lt_or_gt_of_ne (fun e' => hne (hinj e')) with h1 | h1
  · exact absurd e (ne_of_lt ((rankOf_lt_iff hinj i j).2 h1))
  · exact absurd e (ne_of_gt ((rankOf_lt_iff hinj j i).2 h1))

/-- The layer variables of a stacking are those of the permutation of its ranks. -/
lemma xOf_rank {n : ℕ} {h : Fin n → ℤ} (hinj : Function.Injective h) :
    Walk.xOf h = Walk.xOf fun i => ((rankOf h i : ℕ) : ℤ) := by
  funext i j
  simp only [Walk.xOf, Nat.cast_lt, ← Fin.lt_def, rankOf_lt_iff hinj]

namespace Walk

lemma injective_of_flat {n : ℕ} {w : Walk (Fin n) ℚ} (hC : w.C = Finset.univ) {h : Fin n → ℤ}
    (hf : w.IsFlat h) : Function.Injective h := fun a b e =>
  hf.1 (by rw [hC]; exact Finset.mem_coe.2 (Finset.mem_univ a))
    (by rw [hC]; exact Finset.mem_coe.2 (Finset.mem_univ b)) e

/-! ### Example 1: a generic vertex of degree six -/

/-- The vertex of Fig. 1: angles `40, 70, 100, 60, 40, 50`, walk `(40, -30, 70, 10, 50, 0)`. -/
def ex1 : Walk (Fin 6) ℚ where
  C := Finset.univ
  c := ![40, -30, 70, 10, 50, 0]
  two_le := by decide
  zig := by decide

/-- The flat-folded state of Fig. 1(b): `f_3, f_6, f_1, f_2, f_5, f_4` from top to bottom. -/
def fig1 : Fin 6 → ℤ := ![4, 3, 6, 1, 2, 5]

/-- **Example 1.**  The vertex is generic, every two sectors overlap, its rows are the twelve
taco–tortilla rows of the paper, the stacking of Fig. 1(b) is a flat-folded state with
assignment `MMMMVV` and `M - V = 2`, and the vertex has `2^3 = 8` flat-foldable assignments,
those induced by the solutions of the rows (Corollary 1). -/
theorem example1 :
    ex1.Generic ∧ (∀ a b, ex1.Overlap a b) ∧
    ex1.ttRows = {Row.tt 0 1 2, Row.tt 0 1 3, Row.tt 0 1 4, Row.tt 0 1 5,
      Row.tt 3 4 0, Row.tt 3 4 1, Row.tt 3 4 2, Row.tt 3 4 5,
      Row.tt 4 5 2, Row.tt 4 5 3, Row.tt 5 0 1, Row.tt 5 0 2} ∧
    ex1.tcRows = ∅ ∧ ex1.IsFlat fig1 ∧
    ex1.asg (xOf fig1) = (fun k => ![0, 0, 0, 0, 1, 1] k.1) ∧ ex1.mv (ex1.asg (xOf fig1)) = 2 ∧
    ex1.Wflat = ex1.Wlin ∧ ex1.Wflat.ncard = 8 := by
  have hg : ex1.Generic := by
    intro a _ b _ e; revert a b; decide
  have hn := generic_noTC hg
  have hf : ex1.IsFlat fig1 := by
    refine ⟨fun a _ b _ e => by revert a b; decide, ?_⟩
    unfold IsSol; decide
  obtain ⟨h1, -, -, h4⟩ := corollary1 hn ⟨fig1, hf, rfl⟩
  obtain ⟨-, -, h3, -⟩ := corollary1 hn ⟨fig1, hf, rfl⟩
  refine ⟨hg, by decide, by decide, by decide, hf, by decide, by decide, h1, ?_⟩
  rw [h4]
  have : ex1.C.card = 6 := rfl
  have : ex1.gamma = 3 := by omega
  rw [this]; rfl

/-! ### Example 3: a degenerate vertex of degree four -/

/-- The vertex with angles `45, 135, 135, 45`: walk `(45, -90, 45, 0)`, with `e_1` and `e_3`
on one ray. -/
def ex3 : Walk (Fin 4) ℚ where
  C := Finset.univ
  c := ![45, -90, 45, 0]
  two_le := by decide
  zig := by decide

/-- An assignment of the creases `e_1, …, e_4` (`1` is a valley). -/
def asg4 (v : Fin 4 → ZMod 2) : ex3.C → ZMod 2 := fun k => v k.1

/-- The assignments with `M - V = ±2`. -/
def S8 : Finset (ex3.C → ZMod 2) := Finset.univ.filter fun σ => ex3.mv σ = 2 ∨ ex3.mv σ = -2

/-- `VMVV` and `MVMM`. -/
def vmvv : ex3.C → ZMod 2 := asg4 ![1, 0, 1, 1]
def mvmm : ex3.C → ZMod 2 := asg4 ![0, 1, 0, 0]

/-- Six stackings, one for each flat-foldable assignment. -/
def ex3States : List (Fin 4 → ℤ) :=
  [![1, 0, 3, 2], ![3, 0, 1, 2], ![2, 1, 0, 3], ![1, 2, 3, 0], ![0, 3, 2, 1], ![2, 3, 0, 1]]

/-- Two non-transitive solutions of the rows, inducing `VMVV` and `MVMM`. -/
def xVMVV : Fin 4 → Fin 4 → ZMod 2 := ![![0, 1, 0, 1], ![0, 0, 1, 0], ![1, 0, 0, 1], ![0, 1, 0, 0]]
def xMVMM : Fin 4 → Fin 4 → ZMod 2 := ![![0, 0, 1, 0], ![1, 0, 0, 1], ![0, 1, 0, 0], ![1, 0, 1, 0]]

lemma ex3_states : ∀ σ ∈ S8 \ {vmvv, mvmm}, ∃ t ∈ ex3States,
    (∀ a b, t a = t b → a = b) ∧ (∀ r ∈ ex3.rows, r.eval (xOf t) = 0) ∧ ex3.asg (xOf t) = σ := by
  decide +kernel

lemma ex3_sols : ex3.Antisymm xVMVV ∧ ex3.IsSol xVMVV ∧ ex3.asg xVMVV = vmvv ∧
    ex3.Antisymm xMVMM ∧ ex3.IsSol xMVMM ∧ ex3.asg xMVMM = mvmm := by
  unfold Antisymm IsSol; decide

/-- No stacking of the four sectors that satisfies the rows induces `VMVV` or `MVMM`. -/
lemma ex3_exhaust : ∀ p : Fin 4 → Fin 4, (∀ a b, p a = p b → a = b) →
    (∀ r ∈ ex3.rows, r.eval (xOf fun i => ((p i : ℕ) : ℤ)) = 0) →
    ex3.asg (xOf fun i => ((p i : ℕ) : ℤ)) ≠ vmvv ∧ ex3.asg (xOf fun i => ((p i : ℕ) : ℤ)) ≠ mvmm := by
  decide +kernel

/-- **Example 3.**  The rows are `(e_4, f_2)`, `(e_4, f_3)` and the taco–taco row `(e_1, e_3)`;
`W_lin` is the set of the `8` assignments with `M - V = ±2`; `6` of them are flat-foldable, all
but `VMVV` and `MVMM`, which satisfy Maekawa's rule and every linear constraint. -/
theorem example3 :
    ex3.ttRows = {Row.tt 3 0 1, Row.tt 3 0 2} ∧ ex3.tcRows = {Row.tc 0 1 2 3} ∧
    ex3.Wlin = ↑S8 ∧ S8.card = 8 ∧
    ex3.Wflat = ↑(S8 \ {vmvv, mvmm}) ∧ (S8 \ {vmvv, mvmm}).card = 6 := by
  obtain ⟨a1, s1, e1, a2, s2, e2⟩ := ex3_sols
  -- the flat-foldable assignments
  have hflat : ∀ σ ∈ S8 \ {vmvv, mvmm}, σ ∈ ex3.Wflat := by
    intro σ hσ
    obtain ⟨t, -, hi, hs, he⟩ := ex3_states σ hσ
    exact ⟨t, ⟨fun a _ b _ e => hi a b e, hs⟩, he⟩
  -- every flat-folded state avoids `VMVV` and `MVMM`
  have hnot : ∀ h, ex3.IsFlat h → ex3.asg (xOf h) ≠ vmvv ∧ ex3.asg (xOf h) ≠ mvmm := by
    intro h hf
    have hinj := injective_of_flat rfl hf
    have hs : ∀ r ∈ ex3.rows, r.eval (xOf h) = 0 := hf.2
    rw [xOf_rank hinj] at hs ⊢
    exact ex3_exhaust _ (fun a b e => rankOf_injective hinj e) hs
  -- `W_lin` is contained in `M - V = ±2`
  have hlin : ex3.Wlin ⊆ ↑S8 := by
    rintro _ ⟨x, hx, hs, rfl⟩
    have := (corollary3 (w := ex3)).1 x hx hs
    simp only [S8, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact this.2 (Or.inl rfl)
  have hWlin : ex3.Wlin = ↑S8 := by
    refine subset_antisymm hlin fun σ hσ => ?_
    by_cases h : σ ∈ ({vmvv, mvmm} : Finset _)
    · rcases Finset.mem_insert.1 h with rfl | h
      · exact ⟨xVMVV, a1, s1, e1⟩
      · rw [Finset.mem_singleton.1 h]; exact ⟨xMVMM, a2, s2, e2⟩
    · exact Wflat_subset_Wlin (hflat σ (Finset.mem_sdiff.2 ⟨hσ, h⟩))
  refine ⟨by decide, by decide, hWlin, by decide, ?_, by decide⟩
  refine subset_antisymm ?_ fun σ hσ => hflat σ hσ
  rintro _ ⟨h, hf, rfl⟩
  have hσ : ex3.asg (xOf h) ∈ ex3.Wlin := Wflat_subset_Wlin ⟨h, hf, rfl⟩
  rw [hWlin] at hσ
  obtain ⟨n1, n2⟩ := hnot h hf
  simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton]
  exact ⟨hσ, fun e => e.elim n1 n2⟩

/-! ### Example 4: the regular vertex of degree six -/

/-- The vertex with all angles `60`: walk `(60, 0, 60, 0, 60, 0)`. -/
def ex4 : Walk (Fin 6) ℚ where
  C := Finset.univ
  c := ![60, 0, 60, 0, 60, 0]
  two_le := by decide
  zig := by decide

/-- The assignments with `M - V ≡ 2 (mod 4)`. -/
def S32 : Finset (ex4.C → ZMod 2) := Finset.univ.filter fun σ => ex4.mv σ % 4 = 2

/-- All mountains and all valleys. -/
def allM : ex4.C → ZMod 2 := fun _ => 0
def allV : ex4.C → ZMod 2 := fun _ => 1

/-- Thirty stackings, one for each flat-foldable assignment. -/
def ex4States : List (Fin 6 → ℤ) :=
  [![1, 0, 5, 2, 3, 4], ![1, 0, 5, 4, 3, 2], ![3, 0, 5, 4, 1, 2], ![1, 0, 3, 4, 5, 2],
   ![5, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2], ![2, 1, 4, 5, 0, 3], ![3, 2, 1, 0, 5, 4],
   ![5, 2, 1, 0, 3, 4], ![5, 4, 3, 2, 1, 0], ![4, 3, 2, 1, 0, 5], ![3, 2, 1, 4, 5, 0],
   ![2, 1, 0, 3, 4, 5], ![2, 1, 0, 5, 4, 3], ![4, 1, 0, 5, 2, 3], ![1, 2, 3, 0, 5, 4],
   ![3, 4, 5, 0, 1, 2], ![1, 2, 5, 4, 3, 0], ![0, 1, 4, 3, 2, 5], ![1, 2, 3, 4, 5, 0],
   ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 5, 4, 3], ![2, 3, 4, 5, 0, 1], ![1, 4, 3, 2, 5, 0],
   ![0, 3, 2, 1, 4, 5], ![0, 5, 4, 3, 2, 1], ![2, 5, 4, 3, 0, 1], ![0, 5, 2, 3, 4, 1],
   ![4, 5, 0, 1, 2, 3], ![2, 3, 0, 5, 4, 1]]

/-- The all-mountain solution of the paper: every odd sector above every even one,
`f_1 > f_3 > f_5 > f_1` and `f_2 > f_6 > f_4 > f_2`. -/
def xAllM : Fin 6 → Fin 6 → ZMod 2 :=
  ![![0, 0, 0, 0, 1, 0], ![1, 0, 1, 1, 1, 0], ![1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 0], ![1, 1, 1, 0, 1, 0]]

lemma ex4_states : ∀ σ ∈ S32 \ {allM, allV}, ∃ t ∈ ex4States,
    (∀ a b, t a = t b → a = b) ∧ (∀ r ∈ ex4.rows, r.eval (xOf t) = 0) ∧ ex4.asg (xOf t) = σ := by
  decide +kernel

/-- **Example 4.**  The regular vertex has no taco–tortilla row and six taco–taco rows; `E = 0`
and `W_lin` is the set of the `32` assignments with `M - V ≡ 2 (mod 4)`; `30` of them are flat-foldable, all but all-mountain and all-valley; and
the all-mountain assignment comes from the explicit cyclic solution of the paper. -/
theorem example4 :
    ex4.ttRows = ∅ ∧ ex4.tcRows.card = 6 ∧ ex4.AllEq ∧
    ex4.Wlin = ↑S32 ∧ S32.card = 32 ∧
    ex4.Wflat = ↑(S32 \ {allM, allV}) ∧ (S32 \ {allM, allV}).card = 30 ∧
    (ex4.Antisymm xAllM ∧ ex4.IsSol xAllM ∧ ex4.asg xAllM = allM) := by
  have hA : ex4.AllEq := by unfold AllEq len hi lo; decide +kernel
  have hWlin : ex4.Wlin = ↑S32 := by
    rw [(theorem3 (Chain.base hA)).1]
    ext σ
    simp [S32, Chain.W4]
  have hflat : ∀ σ ∈ S32 \ {allM, allV}, σ ∈ ex4.Wflat := by
    intro σ hσ
    obtain ⟨t, -, hi, hs, he⟩ := ex4_states σ hσ
    exact ⟨t, ⟨fun a _ b _ e => hi a b e, hs⟩, he⟩
  refine ⟨by decide, by decide, hA, hWlin, by decide, ?_, by decide, by unfold Antisymm IsSol; decide⟩
  refine subset_antisymm ?_ fun σ hσ => hflat σ hσ
  rintro _ ⟨h, hf, rfl⟩
  have hσ : ex4.asg (xOf h) ∈ ex4.Wlin := Wflat_subset_Wlin ⟨h, hf, rfl⟩
  rw [hWlin] at hσ
  have hm := (corollary3 (w := ex4)).2 h hf
  have hM : ex4.mv allM = 6 := by decide
  have hV : ex4.mv allV = -6 := by decide
  simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton]
  refine ⟨hσ, fun e => ?_⟩
  rcases e with e | e <;> rw [e] at hm <;> [rw [hM] at hm; rw [hV] at hm] <;> omega

end Walk

end Origami
