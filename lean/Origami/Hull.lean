import Origami.Lemma6

/-!
# Hull's crimping recursion

Crimping repeatedly a maximal run of smallest sectors reduces every closed walk to one whose
angles are all equal (Sec. 7 of the paper).  We record such a reduction as a `Chain`, with

* `E`: the number of crimps of runs with `k` even;
* `lab`: a label for every crease, two creases having the same label iff they lie in the same
  block of the recursion (the creases of a crimped run with `k` even form a new block; for `k`
  odd they join the block of `e_⋆ = A`; at the end all the creases form one block);
* `W4`: Hull's recursion with every condition read modulo four, as in the paper.

This file proves that every walk has a chain (`exists_run`, `exists_chain`).
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-! ### Closing the walk -/

/-- The signed steps of a closed walk add up to zero. -/
lemma sum_steps : ∑ k ∈ w.C, (w.c k - w.c (prv w.C k)) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  symm
  apply Finset.sum_nbij' (prv w.C) (nxt w.C)
  · intro k hk; exact w.prv_mem hk
  · intro k hk; exact w.nxt_mem hk
  · intro k hk; exact nxt_prv hk
  · intro k hk; exact prv_nxt hk
  · intro k hk; rfl

/-- The lengths of the sectors going up and going down add up to the same total. -/
lemma sum_len_up : ∑ k ∈ w.C.filter w.up, w.len k = ∑ k ∈ w.C.filter (fun k => ¬ w.up k), w.len k := by
  have h := sum_steps (w := w)
  rw [← Finset.sum_filter_add_sum_filter_not w.C w.up] at h
  have e1 : ∑ k ∈ w.C.filter w.up, (w.c k - w.c (prv w.C k)) = ∑ k ∈ w.C.filter w.up, w.len k :=
    Finset.sum_congr rfl fun k hk => (len_of_up (Finset.mem_filter.1 hk).2).symm
  have e2 : ∑ k ∈ w.C.filter (fun k => ¬ w.up k), (w.c k - w.c (prv w.C k)) =
      - ∑ k ∈ w.C.filter (fun k => ¬ w.up k), w.len k := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k hk => by
      rw [len_of_not_up (Finset.mem_filter.1 hk).1 (Finset.mem_filter.1 hk).2]; ring
  rw [e1, e2] at h
  linarith

/-- A closed walk cannot have all its sectors of one length but one. -/
lemma not_all_but_one {A : ι} (hA : A ∈ w.C) {a : α}
    (h : ∀ g ∈ w.C, g ≠ A → w.len g = a) : w.len A = a := by
  have hu := sum_len_up (w := w)
  have hc := card_filter_up (w := w)
  have key : ∀ (S : Finset ι), S ⊆ w.C → ∑ k ∈ S, w.len k =
      S.card • a + (if A ∈ S then w.len A - a else 0) := by
    intro S hS
    rw [Finset.sum_congr rfl (g := fun k => a + if k = A then w.len A - a else 0) (fun k hk => by
      dsimp only
      by_cases hkA : k = A
      · rw [if_pos hkA, hkA]; ring
      · rw [if_neg hkA, h k (hS hk) hkA, add_zero]), Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_ite_eq']
  rw [key _ (Finset.filter_subset _ _), key _ (Finset.filter_subset _ _), hc] at hu
  by_cases hup : w.up A
  · rw [if_pos (Finset.mem_filter.2 ⟨hA, hup⟩),
      if_neg (fun (h : A ∈ w.C.filter (fun k => ¬ w.up k)) => (Finset.mem_filter.1 h).2 hup)] at hu
    linarith
  · rw [if_neg (fun (h : A ∈ w.C.filter w.up) => hup (Finset.mem_filter.1 h).2),
      if_pos (Finset.mem_filter.2 ⟨hA, hup⟩)] at hu
    linarith

/-! ### Runs exist -/

/-- All the sectors have the same angle. -/
def AllEq (w : Walk ι α) : Prop := ∀ g ∈ w.C, ∀ g' ∈ w.C, w.len g = w.len g'

/-- A walk whose angles are not all equal has a maximal run of smallest sectors. -/
theorem exists_run (h : ¬ w.AllEq) : Nonempty w.RunData := by
  classical
  obtain ⟨g₀, hg₀, hmin⟩ := Finset.exists_min_image w.C w.len w.nonempty
  set a := w.len g₀ with ha
  -- a sector that is not smallest
  have hex : ∃ k ∈ w.C, w.len k ≠ a := by
    by_contra hc; push_neg at hc
    exact h fun g hg g' hg' => (hc g hg).trans (hc g' hg').symm
  -- a non-smallest sector followed by a smallest one
  obtain ⟨A, hA, hA1, hA2⟩ : ∃ A ∈ w.C, w.len A ≠ a ∧ w.len (nxt w.C A) = a := by
    by_contra hc; push_neg at hc
    obtain ⟨k, hk, hka⟩ := hex
    have := cycle_induction (fun k => w.len k ≠ a) hk hka (fun k hk h => hc k hk h) g₀ hg₀
    exact this rfl
  set n := w.C.card with hn
  have h2 := w.two_le
  have hex2 : ∃ j, 1 ≤ j ∧ w.len ((nxt w.C)^[j + 1] A) ≠ a :=
    ⟨n - 1, by omega, by rw [Nat.sub_add_cancel (by omega), iterate_card hA]; exact hA1⟩
  set K := Nat.find hex2 with hK
  obtain ⟨hK1, hK2⟩ := Nat.find_spec hex2
  have hKmin : ∀ j, 1 ≤ j → j < K → w.len ((nxt w.C)^[j + 1] A) = a := by
    intro j hj1 hj2
    by_contra hc
    exact Nat.find_min hex2 hj2 ⟨hj1, hc⟩
  -- every sector of the run has the smallest angle
  have hrun : ∀ i, 1 ≤ i → i ≤ K → w.len ((nxt w.C)^[i] A) = a := by
    intro i hi1 hi2
    rcases Nat.lt_or_ge 1 i with h1 | h1
    · have := hKmin (i - 1) (by omega) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
    · have : i = 1 := by omega
      subst this; exact hA2
  -- the run does not cover all the sectors but `f_A`
  have hKn : K + 2 ≤ n := by
    by_contra hc
    have hKle : K ≤ n - 1 := Nat.find_min' hex2 ⟨by omega, by
      rw [Nat.sub_add_cancel (by omega), iterate_card hA]; exact hA1⟩
    apply hA1
    apply not_all_but_one hA
    intro g hg hgA
    obtain ⟨i, hi, rfl⟩ := exists_iterate hA hg
    have hi0 : i ≠ 0 := fun h0 => hgA (by rw [h0]; rfl)
    exact hrun i (by omega) (by omega)
  exact ⟨{
    A := A
    k := K - 1
    hA := hA
    hcard := by omega
    hmin := fun g hg => by rw [hA2]; exact hmin g hg
    hrun := fun i hi => by rw [hA2]; exact hrun (i + 1) (by omega) (by omega)
    hbigA := by rw [hA2]; exact lt_of_le_of_ne (hmin A hA) (Ne.symm hA1)
    hbigZ := by
      rw [hA2, show K - 1 + 2 = K + 1 by omega]
      exact lt_of_le_of_ne (hmin _ (iterate_mem hA _)) (Ne.symm hK2) }⟩

lemma card_runCrimp_lt (R : w.RunData) : (w.runCrimp R).C.card < w.C.card := by
  rw [runCrimp_C, Finset.card_sdiff_of_subset R.B_subset, R.card_B]
  have := R.hcard
  split_ifs <;> omega

/-! ### Chains of crimps -/

/-- A run of Hull's recursion: crimps of maximal runs of smallest sectors, down to a walk with
all angles equal. -/
inductive Chain : Walk ι α → Type _
  | base {w : Walk ι α} : w.AllEq → Chain w
  | step {w : Walk ι α} (R : w.RunData) : Chain (w.runCrimp R) → Chain w

/-- Every walk has a chain. -/
theorem exists_chain : ∀ (n : ℕ) (w : Walk ι α), w.C.card = n → Nonempty (Chain w) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn
  by_cases h : w.AllEq
  · exact ⟨Chain.base h⟩
  · obtain ⟨R⟩ := exists_run h
    obtain ⟨c⟩ := ih _ (hn ▸ card_runCrimp_lt R) (w.runCrimp R) rfl
    exact ⟨Chain.step R c⟩

namespace Chain

/-- `E`: the number of crimped runs with `k` even. -/
def E : {w : Walk ι α} → Chain w → ℕ
  | _, base _ => 0
  | _, step R c => c.E + if Even R.k then 1 else 0

/-- The block of every crease in Hull's recursion, named by one of its creases. -/
def lab : {w : Walk ι α} → Chain w → ι → ι
  | w, base _ => fun _ => w.C.min' w.nonempty
  | _, step R c => fun j => if j ∈ R.B then (if Even R.k then R.A else c.lab R.A) else c.lab j

/-- `M - V` on a set of creases. -/
def mvOn (σ : w.C → ZMod 2) (S : Finset ι) : ℤ :=
  (S.card : ℤ) - 2 * ((Finset.univ.filter fun j : w.C => j.1 ∈ S ∧ σ j = 1).card : ℤ)

/-- The assignment of the crease `e_⋆ = A` fixed by the creases of a run with `k` odd:
`M - V ≡ σ_⋆ (mod 4)` on them, with `0` for a mountain (`+1`) and `1` for a valley. -/
def starVal (R : w.RunData) (σ : w.C → ZMod 2) : ZMod 2 :=
  if mvOn σ (insert R.A R.B) % 4 = 1 then 0 else 1

/-- The assignment induced on the crimped walk. -/
def restrict (R : w.RunData) (σ : w.C → ZMod 2) : (w.runCrimp R).C → ZMod 2 :=
  fun j => if Even R.k ∨ j.1 ≠ R.A then σ ⟨j.1, (Finset.mem_sdiff.1 j.2).1⟩ else starVal R σ

/-- `W₄`: Hull's recursion with every condition read modulo four. -/
def W4 : {w : Walk ι α} → Chain w → Set (w.C → ZMod 2)
  | w, base _ => {σ | w.mv σ % 4 = 2}
  | _, step R c =>
    {σ | (Even R.k → mvOn σ R.B % 4 = 0) ∧ restrict R σ ∈ c.W4}

/-- The labels are creases. -/
lemma lab_mem : ∀ {w : Walk ι α} (c : Chain w) {j : ι}, j ∈ w.C → c.lab j ∈ w.C
  | w, base _, _, _ => Finset.min'_mem _ _
  | w, step R c, j, hj => by
    simp only [lab]
    have hsub : (w.runCrimp R).C ⊆ w.C := Finset.sdiff_subset
    split_ifs with h1 h2
    · exact R.hA
    · have hA' : R.A ∈ (w.runCrimp R).C := by
        have := R.star_mem'; rwa [R.star_odd h2] at this
      exact hsub (c.lab_mem hA')
    · exact hsub (c.lab_mem (R.mem_C'.2 ⟨hj, h1⟩))

/-- **Components refine the blocks of Hull's recursion** (Lemma 4, iterated): two creases
whose adjacent pairs are connected in the hypergraph of the rows lie in the same block. -/
theorem lab_eq_of_sameComp : ∀ {w : Walk ι α} (c : Chain w) {j j' : ι}, j ∈ w.C → j' ∈ w.C →
    w.SameComp j j' → c.lab j = c.lab j'
  | _, base _, _, _, _, _, _ => rfl
  | w, step R c, j, j', hj, hj', h => by
    simp only [lab]
    by_cases hk : Even R.k
    · obtain ⟨h1, h2⟩ := lemma6_even R hk hj hj' h
      by_cases hjB : j ∈ R.B
      · rw [if_pos hjB, if_pos (h1.1 hjB)]
      · rw [if_neg hjB, if_neg (fun h => hjB (h1.2 h))]
        exact c.lab_eq_of_sameComp (R.mem_C'.2 ⟨hj, hjB⟩)
          (R.mem_C'.2 ⟨hj', fun h => hjB (h1.2 h)⟩) (h2 hjB)
    · have h1 := lemma6_odd R hk hj hj' h
      have hA' : R.A ∈ (w.runCrimp R).C := by
        have := R.star_mem'; rwa [R.star_odd hk] at this
      have hred : ∀ {x}, x ∈ w.C → (if x ∈ R.B then R.A else x) ∈ (w.runCrimp R).C := by
        intro x hx; split_ifs with hb
        · exact hA'
        · exact R.mem_C'.2 ⟨hx, hb⟩
      have := c.lab_eq_of_sameComp (hred hj) (hred hj') h1
      simp only [if_neg hk]
      split_ifs at this ⊢ <;> exact this

end Chain

/-! ### Lifting flat-folded states along a run -/

/-- Two walks with the same creases and positions are equal. -/
theorem ext {w₁ w₂ : Walk ι α} (hC : w₁.C = w₂.C) (hc : w₁.c = w₂.c) : w₁ = w₂ := by
  cases w₁; cases w₂; simp only at hC hc; subst hC; subst hc; rfl

namespace RunData

variable (R : w.RunData)

/-- Along the run, the positions repeat with period two. -/
lemma c_t_two {i : ℕ} (hi : i + 2 ≤ R.k + 1) : w.c (R.t (i + 2)) = w.c (R.t i) := by
  have l1 := R.hrun i (by omega)
  have l2 := R.hrun (i + 1) (by omega)
  have u1 : w.up (R.t (i + 1)) ↔ ¬ w.up (R.t i) := by rw [R.t_succ]; exact up_nxt (R.t_mem i)
  have u2 : w.up (R.t (i + 2)) ↔ ¬ w.up (R.t (i + 1)) := by
    rw [R.t_succ]; exact up_nxt (R.t_mem _)
  by_cases hu : w.up (R.t (i + 1))
  · rw [len_of_up hu, R.prv_t_succ] at l1
    have hu2 : ¬ w.up (R.t (i + 2)) := fun h => u2.1 h hu
    rw [len_of_not_up (R.t_mem _) hu2, R.prv_t_succ] at l2
    linarith
  · rw [len_of_not_up (R.t_mem _) hu, R.prv_t_succ] at l1
    have hu2 : w.up (R.t (i + 2)) := u2.2 hu
    rw [len_of_up hu2, R.prv_t_succ] at l2
    linarith

/-- The run sectors are legal single crimps. -/
lemma crimpOK_t {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ R.k + 1) (h4 : 4 ≤ w.C.card) :
    w.CrimpOK (R.t i) where
  mem := R.t_mem i
  four := h4
  le_prv := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [R.hrun j (by omega)]; exact R.hmin _ (w.prv_mem (R.t_mem _))
  le_nxt := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [R.hrun j (by omega)]; exact R.hmin _ (w.nxt_mem (R.t_mem _))

lemma four_le (hk : 1 ≤ R.k ∨ Even R.k) : 4 ≤ w.C.card := by
  rcases hk with hk | hk
  · have := R.hcard; omega
  · have := R.card_even_ge hk; omega

end RunData

/-! #### Crimping the last sector of a run -/

namespace RunData

section last

variable (R : w.RunData) (hk2 : 2 ≤ R.k) (hc : w.CrimpOK (R.t (R.k + 1)))

lemma t_ne {i j : ℕ} (hi : i ≤ R.k + 2) (hj : j ≤ R.k + 2) (h : i ≠ j) : R.t i ≠ R.t j :=
  fun e => h (R.t_inj (by have := R.hcard; omega) (by have := R.hcard; omega) e)

include hk2 in
lemma prv_last : prv w.C (R.t (R.k + 1)) = R.t R.k := R.prv_t_succ R.k

include hk2 in
lemma prvprv_last : prv w.C (prv w.C (R.t (R.k + 1))) = R.t (R.k - 1) := by
  rw [prv_last R hk2, show R.k = R.k - 1 + 1 by omega, R.prv_t_succ]; simp

include hk2 hc

lemma mem_C1 {i : ℕ} (hi : i + 2 ≤ R.k + 1 ∨ i = R.k + 2) : R.t i ∈ (w.crimp _ hc).C := by
  rw [crimp_C, mem_crimpC, prv_last R hk2]
  exact ⟨R.t_ne (by omega) (by omega) (by omega), R.t_ne (by omega) (by omega) (by omega),
    R.t_mem i⟩

/-- In the crimped walk the run starts with the same creases. -/
lemma iter1 : ∀ i, i + 1 ≤ R.k → (nxt (w.crimp _ hc).C)^[i] R.A = R.t i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), crimp_C,
      crimpC_nxt hc (mem_C1 R hk2 hc (i := i) (by omega)), prvprv_last R hk2,
      if_neg (R.t_ne (by omega) (by omega) (by omega)), ← R.t_succ]

lemma iter1_k : (nxt (w.crimp _ hc).C)^[R.k] R.A = R.t (R.k + 2) := by
  rw [show (nxt (w.crimp _ hc).C)^[R.k] R.A = (nxt (w.crimp _ hc).C)^[R.k - 1 + 1] R.A from by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ R.k)]]
  rw [Function.iterate_succ_apply', iter1 R hk2 hc (R.k - 1) (by omega), crimp_C,
    crimpC_nxt hc (mem_C1 R hk2 hc (i := R.k - 1) (by omega)), prvprv_last R hk2, if_pos rfl,
    ← R.t_succ]

/-- Crimping the last run sector changes no angle. -/
lemma len1 {g : ι} (hg : g ∈ (w.crimp _ hc).C) : (w.crimp _ hc).len g = w.len g := by
  unfold len lo hi
  rw [crimp_C, crimpC_prv hc hg, crimp_c]
  split_ifs with h
  · have hg' : prv w.C g = R.t (R.k + 1) := by rw [h, prv_nxt (R.t_mem _)]
    rw [prvprv_last R hk2, hg']
    have := R.c_t_two (i := R.k - 1) (by omega)
    rw [show R.k - 1 + 2 = R.k + 1 by omega] at this
    rw [this]
  · rfl

/-- The shorter run left after crimping its last sector. -/
def R1 : (w.crimp _ hc).RunData :=
  have hA1 : R.A ∈ (w.crimp _ hc).C := mem_C1 R hk2 hc (i := 0) (by omega)
  have ht1 : R.t 1 ∈ (w.crimp _ hc).C := mem_C1 R hk2 hc (i := 1) (by omega)
  have e1 : nxt (w.crimp _ hc).C R.A = R.t 1 := iter1 R hk2 hc 1 (by omega)
  { A := R.A
    k := R.k - 2
    hA := hA1
    hcard := by rw [crimp_C, card_crimpC hc]; have := R.hcard; omega
    hmin := fun g hg => by
      rw [e1, len1 R hk2 hc ht1, len1 R hk2 hc hg]
      exact R.hmin g (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg))
    hrun := fun i hi => by
      have hi' : i ≤ R.k - 2 := hi
      have hti : R.t (i + 1) ∈ (w.crimp _ hc).C := mem_C1 R hk2 hc (i := i + 1) (by omega)
      rw [iter1 R hk2 hc (i + 1) (by omega), e1, len1 R hk2 hc hti, len1 R hk2 hc ht1]
      exact R.hrun i (by omega)
    hbigA := by
      rw [e1, len1 R hk2 hc ht1, len1 R hk2 hc hA1]
      exact R.hbigA
    hbigZ := by
      have hZ1 : R.t (R.k + 2) ∈ (w.crimp _ hc).C := mem_C1 R hk2 hc (i := R.k + 2) (Or.inr rfl)
      rw [e1, show R.k - 2 + 2 = R.k by omega, iter1_k R hk2 hc, len1 R hk2 hc ht1,
        len1 R hk2 hc hZ1]
      exact R.hbigZ }

lemma R1_k : (R1 R hk2 hc).k = R.k - 2 := rfl

lemma R1_t {i : ℕ} (hi : i + 1 ≤ R.k) : (R1 R hk2 hc).t i = R.t i := iter1 R hk2 hc i hi

lemma R1_even : Even (R1 R hk2 hc).k ↔ Even R.k := by
  rw [R1_k]
  obtain ⟨m, hm⟩ : ∃ m, R.k = m + 2 := ⟨R.k - 2, by omega⟩
  rw [hm, Nat.add_sub_cancel, Nat.even_add]; simp

/-- Crimping the shorter run gives the same walk. -/
lemma runCrimp_R1 : (w.crimp _ hc).runCrimp (R1 R hk2 hc) = w.runCrimp R := by
  refine ext ?_ rfl
  ext x
  simp only [runCrimp_C, crimp_C, Finset.mem_sdiff, mem_crimpC, prv_last R hk2]
  rw [R.mem_B, (R1 R hk2 hc).mem_B]
  simp only [R1_even R hk2 hc]
  constructor
  · rintro ⟨⟨h1, h2, hx⟩, h3⟩
    refine ⟨hx, ?_⟩
    rintro ⟨i, hi1, hi2, rfl⟩
    by_cases hik : i + 1 ≤ R.k
    · exact h3 ⟨i, hi1, by rw [R1_k]; omega, (R1_t R hk2 hc hik).symm⟩
    · rcases (show i = R.k ∨ i = R.k + 1 by omega) with rfl | rfl
      · exact h2 rfl
      · exact h1 rfl
  · rintro ⟨hx, h3⟩
    refine ⟨⟨fun e => h3 ⟨R.k + 1, by split_ifs <;> omega, le_rfl, e⟩,
      fun e => h3 ⟨R.k, by split_ifs <;> omega, by omega, e⟩, hx⟩, ?_⟩
    rintro ⟨i, hi1, hi2, rfl⟩
    rw [R1_k] at hi2
    exact h3 ⟨i, hi1, by omega, R1_t R hk2 hc (by omega)⟩

end last

/-- **Lifting a flat-folded state along a run.**  Every flat-folded state of the crimped walk
lifts to one of the walk that agrees with it at every surviving crease and gives every deleted
crease the layer value `0` (the run folded as a fixed accordion). -/
theorem runLift : ∀ (n : ℕ) (w : Walk ι α) (R : w.RunData), R.k = n →
    ∀ {h' : ι → ℤ}, (w.runCrimp R).IsFlat h' → ∃ h, w.IsFlat h ∧
      (∀ j ∈ (w.runCrimp R).C, xOf h j (nxt w.C j) = xOf h' j (nxt (w.runCrimp R).C j)) ∧
      (∀ j ∈ R.B, xOf h j (nxt w.C j) = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w R hn h' hf
  by_cases hk2 : 2 ≤ R.k
  · have hc := R.crimpOK_t (i := R.k + 1) (by omega) le_rfl (R.four_le (Or.inl (by omega)))
    have e := runCrimp_R1 R hk2 hc
    obtain ⟨h1, hf1, ha1, hb1⟩ := ih (R.k - 2) (by omega) (w.crimp _ hc) (R1 R hk2 hc)
      (R1_k R hk2 hc)
      (h' := h') (by rw [e]; exact hf)
    obtain ⟨h, hf2, ha2, hv1, hv2⟩ := hc.exists_lift hf1 false
    refine ⟨h, hf2, ?_, ?_⟩
    · intro j hj
      have hj1 : j ∈ (w.crimp _ hc).C := by
        rw [← e] at hj; exact (Finset.mem_sdiff.1 hj).1
      rw [ha2 j hj1, ha1 j (by rw [e]; exact hj), e]
    · intro j hj
      by_cases hj1 : j ∈ (w.crimp _ hc).C
      · rw [ha2 j hj1]
        apply hb1
        rw [(R1 R hk2 hc).mem_B]
        simp only [R1_even R hk2 hc]
        obtain ⟨i, hi1, hi2, rfl⟩ := R.mem_B.1 hj
        have hik : i + 1 ≤ R.k := by
          by_contra hc'
          rw [crimp_C, mem_crimpC, prv_last R hk2] at hj1
          rcases (show i = R.k ∨ i = R.k + 1 by omega) with rfl | rfl
          · exact hj1.2.1 rfl
          · exact hj1.1 rfl
        exact ⟨i, hi1, by rw [R1_k]; omega, (R1_t R hk2 hc (by omega)).symm⟩
      · rw [crimp_C, mem_crimpC, prv_last R hk2] at hj1
        push_neg at hj1
        by_cases h1 : j = R.t (R.k + 1)
        · rw [h1]; simpa using hv2
        · have h2 := hj1 h1
          by_cases h3 : j = R.t R.k
          · rw [h3, ← R.t_succ]
            have := hv1; rw [prv_last R hk2] at this; simpa using this
          · exact absurd (R.B_subset hj) (h2 h3)
  · -- `k = 0` or `k = 1`: one single crimp
    have hc := R.crimpOK_t (i := R.k + 1) (by omega) le_rfl
      (R.four_le (by rcases Nat.lt_or_ge R.k 1 with h | h <;> [right; left] <;>
        [exact ⟨0, by omega⟩; omega]))
    have hpa : prv w.C (R.t (R.k + 1)) = R.t R.k := R.prv_t_succ R.k
    have hBeq : R.B = {R.t R.k, R.t (R.k + 1)} := by
      ext x
      rw [R.mem_B]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨i, hi1, hi2, rfl⟩
        split_ifs at hi1 with hk
        · rcases (show R.k = 0 by obtain ⟨m, hm⟩ := hk; omega) with h0
          rw [h0] at hi2 ⊢
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp
        · rcases (show R.k = 1 by by_contra h; exact hk ⟨0, by omega⟩) with h1
          rw [h1] at hi2 ⊢
          rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl <;> simp
      · rintro (rfl | rfl)
        · refine ⟨R.k, ?_, by omega, rfl⟩
          split_ifs with hk <;> [omega; (by_contra h; exact hk ⟨0, by omega⟩)]
        · refine ⟨R.k + 1, by split_ifs <;> omega, le_rfl, rfl⟩
    have e : w.crimp _ hc = w.runCrimp R := by
      refine ext ?_ rfl
      ext x
      simp only [crimp_C, mem_crimpC, runCrimp_C, Finset.mem_sdiff, hBeq, hpa,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    obtain ⟨h, hf2, ha2, hv1, hv2⟩ := hc.exists_lift (h' := h') (by rw [e]; exact hf) false
    refine ⟨h, hf2, fun j hj => by rw [← e] at hj ⊢; exact ha2 j hj, ?_⟩
    intro j hj
    rw [hBeq] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · rw [← R.t_succ]; have := hv1; rw [hpa] at this; simpa using this
    · simpa using hv2

end RunData

end Walk

end Origami

