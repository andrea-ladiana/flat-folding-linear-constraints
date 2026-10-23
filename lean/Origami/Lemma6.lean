import Origami.Run

/-!
# Lemma 4: crimping a run never merges two components

Let `w'` be obtained from `w` by crimping a maximal run of smallest sectors.  The paper
defines a map `ψ` from the vertices of `H_w` to the components of `H_{w'}` (and an extra
symbol `β` when `k` is even, or "undefined" when `k` is odd, Table 1) such that all the
defined vertices of a row of `w` have the same image.  Hence connected adjacent pairs of `w`
have the same image, and we read off:

* `k` even: the adjacent pairs of the deleted creases form components of their own, and two
  surviving creases connected in `H_w` are connected in `H_{w'}`;
* `k` odd: two creases connected in `H_w` are connected in `H_{w'}` once every deleted
  crease is replaced by `A` (the crease `e_⋆`).

This *refinement* statement implies the inequalities `γ(w) ≥ γ(w') + [k even]` of the paper.
As in the paper we first assume that `A` is a maximum; reflection removes the assumption.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

namespace RunData

variable (R : w.RunData)

/-- The sectors `f_A`, the run and `f_Z`. -/
def Q : Finset ι := (Finset.range (R.k + 3)).image R.t

lemma mem_Q {x : ι} : x ∈ R.Q ↔ ∃ i, i ≤ R.k + 2 ∧ x = R.t i := by
  unfold Q; simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩

lemma t_mem_Q {i : ℕ} (hi : i ≤ R.k + 2) : R.t i ∈ R.Q := R.mem_Q.2 ⟨i, hi, rfl⟩

lemma B_subset_Q : R.B ⊆ R.Q := by
  intro q hq
  obtain ⟨i, -, hi, rfl⟩ := R.mem_B.1 hq
  exact R.t_mem_Q (by omega)

/-- The crease `prv A`. -/
abbrev P : ι := prv w.C R.A

section big

variable {R} (hn : R.k + 4 ≤ w.C.card)
include hn

lemma t_not_mem_Q {i : ℕ} (h1 : R.k + 2 < i) (h2 : i < w.C.card) : R.t i ∉ R.Q := by
  intro hm
  obtain ⟨j, hj, e⟩ := R.mem_Q.1 hm
  have := R.t_inj h2 (by omega) e
  omega

lemma P_not_mem_Q : R.P ∉ R.Q := by
  rw [show R.P = R.t (w.C.card - 1) from R.prvA_eq]
  exact t_not_mem_Q hn (by omega) (by omega)

lemma nZ_not_mem_Q : nxt w.C R.Z ∉ R.Q := by
  rw [← R.t_succ]; exact t_not_mem_Q hn (by omega) (by omega)

lemma nZ_eq : nxt w.C R.Z = R.t (R.k + 3) := (R.t_succ _).symm

/-- The four kinds of creases: outer creases, `prv A`, `Z`, and the creases `t i`,
`i ≤ k + 1`, both of whose sectors lie in `Q`. -/
lemma crease_cases {q : ι} (hq : q ∈ w.C) :
    (q ∉ R.Q ∧ nxt w.C q ∉ R.Q) ∨ q = R.P ∨ q = R.Z ∨ (∃ i, i ≤ R.k + 1 ∧ q = R.t i) := by
  by_cases h1 : q ∈ R.Q
  · obtain ⟨i, hi, rfl⟩ := R.mem_Q.1 h1
    by_cases h2 : i = R.k + 2
    · right; right; left; rw [h2]
    · right; right; right; exact ⟨i, by omega, rfl⟩
  · by_cases h2 : nxt w.C q ∈ R.Q
    · obtain ⟨i, hi, e⟩ := R.mem_Q.1 h2
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · right; left
        have h3 := prv_nxt (C := w.C) hq
        rw [e, h0] at h3; exact h3.symm
      · exfalso; apply h1
        have h3 := prv_nxt (C := w.C) hq
        rw [e] at h3
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [R.prv_t_succ] at h3
        rw [← h3]; exact R.t_mem_Q (by omega)
    · left; exact ⟨h1, h2⟩

end big

/-! #### Intervals, when `A` is a maximum -/

section up

variable {R} (hup : w.up R.A)
include hup

/-- The upper position `h` of the run. -/
abbrev hh : α := w.c R.A
/-- The lower position `ℓ = h - α` of the run. -/
abbrev ll : α := w.c R.A - R.al

lemma c_t {i : ℕ} (hi : i ≤ R.k + 1) :
    w.c (R.t i) = if Even i then w.c R.A else w.c R.A - R.al := (R.pos hup i hi).2

lemma up_t {i : ℕ} (hi : i ≤ R.k + 1) : w.up (R.t i) ↔ Even i := (R.pos hup i hi).1

lemma c_t_mem {i : ℕ} (hi : i ≤ R.k + 1) : w.c (R.t i) = w.c R.A ∨ w.c (R.t i) = w.c R.A - R.al := by
  rw [c_t hup hi]; split_ifs <;> simp

/-- The run sectors have the interval `J = [ℓ, h]`. -/
lemma lohi_run {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.k + 1) :
    w.lo (R.t i) = w.c R.A - R.al ∧ w.hi (R.t i) = w.c R.A := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have a1 := c_t hup (i := j) (by omega)
  have a2 := c_t hup (i := j + 1) h2
  have al := R.al_pos
  unfold lo hi
  rw [R.prv_t_succ, a1, a2]
  by_cases he : Even j
  · rw [if_pos he, if_neg (by rw [Nat.even_add_one]; exact not_not.2 he)]
    exact ⟨min_eq_right (by linarith), max_eq_left (by linarith)⟩
  · rw [if_neg he, if_pos (by rw [Nat.even_add_one]; exact he)]
    exact ⟨min_eq_left (by linarith), max_eq_right (by linarith)⟩

lemma lohi_A : w.lo R.A = w.c R.P ∧ w.hi R.A = w.c R.A := lo_hi_of_up hup

lemma lohi_Z_even (hk : Even R.k) : w.lo R.Z = w.c R.A - R.al ∧ w.hi R.Z = w.c R.Z := by
  obtain ⟨-, hu⟩ := (R.c_Z hup).1 hk
  have := lo_hi_of_up hu
  rw [this.1, this.2, R.prv_t_succ, c_t hup le_rfl,
    if_neg (by rw [Nat.even_add_one]; exact not_not.2 hk)]
  exact ⟨rfl, rfl⟩

lemma lohi_Z_odd (hk : ¬ Even R.k) : w.lo R.Z = w.c R.Z ∧ w.hi R.Z = w.c R.A := by
  obtain ⟨-, hu⟩ := (R.c_Z hup).2 hk
  have := lo_hi_of_not_up R.Z_mem hu
  rw [this.1, this.2, R.prv_t_succ, c_t hup le_rfl,
    if_pos (by rw [Nat.even_add_one]; exact hk)]
  exact ⟨rfl, rfl⟩

/-- For `k` even, the intervals of the sectors of `Q` lie inside `[c (prv A), c Z]`, the
interval of the merged sector. -/
lemma Q_bounds (hk : Even R.k) {g : ι} (hg : g ∈ R.Q) :
    w.c R.P ≤ w.lo g ∧ w.hi g ≤ w.c R.Z := by
  obtain ⟨i, hi, rfl⟩ := R.mem_Q.1 hg
  have hP := R.c_prvA hup
  have hZ := (R.c_Z hup).1 hk
  have al := R.al_pos
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    obtain ⟨e1, e2⟩ := lohi_A hup
    show w.c R.P ≤ w.lo R.A ∧ w.hi R.A ≤ w.c R.Z
    rw [e1, e2]; exact ⟨le_rfl, hZ.1.le⟩
  by_cases hiZ : i = R.k + 2
  · subst hiZ
    obtain ⟨e1, e2⟩ := lohi_Z_even hup hk
    rw [e1, e2]; exact ⟨by linarith, le_rfl⟩
  · obtain ⟨e1, e2⟩ := lohi_run hup hpos (by omega)
    rw [e1, e2]; exact ⟨by linarith, hZ.1.le⟩

end up

/-! #### The crimped walk `w'` -/

lemma mem_C' {q : ι} : q ∈ (w.runCrimp R).C ↔ q ∈ w.C ∧ q ∉ R.B := by
  simp [runCrimp_C, Finset.mem_sdiff]

lemma mem_C'_of {q : ι} (hq : q ∈ w.C) (hqQ : q ∉ R.Q) : q ∈ (w.runCrimp R).C :=
  R.mem_C'.2 ⟨hq, fun h => hqQ (R.B_subset_Q h)⟩

lemma Z_mem' : R.Z ∈ (w.runCrimp R).C := R.mem_C'.2 ⟨R.Z_mem, R.Z_not_mem_B⟩

lemma star_mem' : R.star ∈ (w.runCrimp R).C := R.mem_C'.2 ⟨R.star_mem, R.star_not_mem_B⟩

lemma nxt' {q : ι} (hq : q ∈ (w.runCrimp R).C) :
    nxt (w.runCrimp R).C q = if q = R.star then R.Z else nxt w.C q := by
  split_ifs with h
  · rw [h]; exact R.nxt_star
  · exact R.nxt_other (R.mem_C'.1 hq).1 (R.mem_C'.1 hq).2 h

lemma prv' {q : ι} (hq : q ∈ (w.runCrimp R).C) :
    prv (w.runCrimp R).C q = if q = R.Z then R.star else prv w.C q := by
  split_ifs with h
  · rw [h]; exact R.prv_Z
  · exact R.prv_other (R.mem_C'.1 hq).1 (R.mem_C'.1 hq).2 h

lemma lohi' {g : ι} (hg : g ∈ (w.runCrimp R).C) (hgZ : g ≠ R.Z) :
    (w.runCrimp R).lo g = w.lo g ∧ (w.runCrimp R).hi g = w.hi g := by
  unfold lo hi; rw [R.prv' hg, if_neg hgZ]; exact ⟨rfl, rfl⟩

lemma star_even (hk : Even R.k) : R.star = R.P := by unfold star; rw [if_pos hk]
lemma star_odd (hk : ¬ Even R.k) : R.star = R.A := by unfold star; rw [if_neg hk]

section up

variable {R} (hup : w.up R.A)
include hup

lemma lohi'_Z_even (hk : Even R.k) :
    (w.runCrimp R).lo R.Z = w.c R.P ∧ (w.runCrimp R).hi R.Z = w.c R.Z := by
  have hP := R.c_prvA hup
  have hZ := ((R.c_Z hup).1 hk).1
  have al := R.al_pos
  unfold lo hi
  rw [R.prv' R.Z_mem', if_pos rfl, R.star_even hk, runCrimp_c]
  exact ⟨min_eq_left (by linarith), max_eq_right (by linarith)⟩

lemma lohi'_Z_odd (hk : ¬ Even R.k) :
    (w.runCrimp R).lo R.Z = w.lo R.Z ∧ (w.runCrimp R).hi R.Z = w.hi R.Z := by
  unfold lo hi
  rw [R.prv' R.Z_mem', if_pos rfl, R.star_odd hk, runCrimp_c, R.prv_t_succ,
    c_t hup le_rfl, if_pos (by rw [Nat.even_add_one]; exact hk)]
  exact ⟨rfl, rfl⟩

/-- Crimping a run does not change the type of a surviving crease. -/
lemma up' {q : ι} (hq : q ∈ (w.runCrimp R).C) : (w.runCrimp R).up q ↔ w.up q := by
  unfold up
  rw [R.prv' hq, runCrimp_c]
  split_ifs with h
  · subst h
    by_cases hk : Even R.k
    · obtain ⟨h1, h2⟩ := (R.c_Z hup).1 hk
      rw [R.star_even hk]
      have hP := R.c_prvA hup; have al := R.al_pos
      exact ⟨fun _ => h2, fun _ => by linarith⟩
    · obtain ⟨h1, h2⟩ := (R.c_Z hup).2 hk
      rw [R.star_odd hk]
      have al := R.al_pos
      constructor
      · intro h; exfalso; linarith
      · intro h; exact absurd h h2
  · rfl

end up

/-! #### Rows of `w'` -/

/-- The component of `H_{w'}` containing a pair. -/
abbrev cl (u : Sym2 ι) : Quot (w.runCrimp R).Linked := Quot.mk _ u

lemma cl_eq {r : Row ι} (hr : r ∈ (w.runCrimp R).rows) {u v : Sym2 ι} (hu : u ∈ r.verts)
    (hv : v ∈ r.verts) : R.cl u = R.cl v := Quot.sound ⟨r, hr, hu, hv⟩

/-- Two pairs on a taco–tortilla row of `w'`. -/
lemma cl_tt {q g : ι} (h : (w.runCrimp R).IsTT q g) :
    R.cl s(q, g) = R.cl s(nxt (w.runCrimp R).C q, g) :=
  R.cl_eq (tt_mem_rows h) (by rw [Row.mem_verts_tt]; left; rfl)
    (by rw [Row.mem_verts_tt]; right; rfl)

/-- The four pairs of a taco–taco row of `w'` are in one component. -/
lemma cl_tc {q l : ι} (h : (w.runCrimp R).IsTC q l) {a b : ι}
    (ha : a = q ∨ a = nxt (w.runCrimp R).C q) (hb : b = l ∨ b = nxt (w.runCrimp R).C l) :
    R.cl s(a, b) = R.cl s(q, l) := by
  rcases lt_or_gt_of_ne h.2.2.1 with hql | hql
  · have hr := tc_mem_rows hql h
    exact R.cl_eq hr (s_mem_tc_of ⟨ha, hb⟩) (s_mem_tc_of ⟨Or.inl rfl, Or.inl rfl⟩)
  · have h' : (w.runCrimp R).IsTC l q := ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.1.symm,
      h.2.2.2.2.symm⟩
    have hr := tc_mem_rows hql h'
    exact R.cl_eq hr (s_mem_tc_of' ⟨hb, ha⟩) (s_mem_tc_of' ⟨Or.inl rfl, Or.inl rfl⟩)

lemma cl_swap (a b : ι) : R.cl s(a, b) = R.cl s(b, a) := by rw [Sym2.eq_swap]

/-! #### `k` even -/

/-- The map `ψ` for `k` even; `none` is the extra symbol `β` (Table 1, first column). -/
def psiE (x y : ι) : Option (Quot (w.runCrimp R).Linked) :=
  if x ∈ R.Q then (if y ∈ R.Q then none else some (R.cl s(R.Z, y)))
  else if y ∈ R.Q then some (R.cl s(R.Z, x)) else some (R.cl s(x, y))

lemma psiE_symm (x y : ι) : R.psiE x y = R.psiE y x := by
  unfold psiE; split_ifs <;> simp [cl_swap]

section even

variable {R} (hk : Even R.k) (hup : w.up R.A)
include hk hup

lemma ns_of_outer {q : ι} (hq : q ∈ w.C) (hq2 : nxt w.C q ∉ R.Q) : q ≠ R.star := by
  rw [R.star_even hk]; intro e; apply hq2; rw [e, nxt_prv R.hA]; exact R.t_mem_Q (i := 0) (by omega)

/-- A position at one end of the run lies inside the merged sector. -/
lemma in_merged {p : α} (hp : p = w.c R.A ∨ p = w.c R.A - R.al) :
    (w.runCrimp R).lo R.Z < p ∧ p < (w.runCrimp R).hi R.Z := by
  rw [(lohi'_Z_even hup hk).1, (lohi'_Z_even hup hk).2]
  have hP := R.c_prvA hup; have hZ := ((R.c_Z hup).1 hk).1; have al := R.al_pos
  rcases hp with rfl | rfl <;> constructor <;> linarith

lemma psiE_tt {q g : ι} (h : w.IsTT q g) : R.psiE q g = R.psiE (nxt w.C q) g := by
  have hn := R.card_even_ge hk
  obtain ⟨hq, hg, i1, i2⟩ := h
  have hP := R.c_prvA hup; have hZ := ((R.c_Z hup).1 hk).1; have al := R.al_pos
  have hAQ : R.A ∈ R.Q := R.t_mem_Q (i := 0) (by omega)
  have hZQ : R.Z ∈ R.Q := R.t_mem_Q le_rfl
  rcases crease_cases hn hq with ⟨hq1, hq2⟩ | hqP | hqZ | ⟨i, hi, rfl⟩
  · have hq' := R.mem_C'_of hq hq1
    have hn' : nxt (w.runCrimp R).C q = nxt w.C q := by
      rw [R.nxt' hq', if_neg (ns_of_outer hk hup hq hq2)]
    by_cases hgQ : g ∈ R.Q
    · simp only [psiE, hq1, hq2, hgQ, if_true, if_false, Option.some.injEq]
      have b := Q_bounds hup hk hgQ
      have htt : (w.runCrimp R).IsTT q R.Z := ⟨hq', R.Z_mem',
        by rw [(lohi'_Z_even hup hk).1, runCrimp_c]; linarith,
        by rw [(lohi'_Z_even hup hk).2, runCrimp_c]; linarith⟩
      have := R.cl_tt htt
      rw [hn'] at this
      rw [cl_swap, this, cl_swap]
    · simp only [psiE, hq1, hq2, hgQ, if_true, if_false, Option.some.injEq]
      have hg' := R.mem_C'_of hg hgQ
      have hgZ : g ≠ R.Z := fun e => hgQ (e ▸ hZQ)
      have htt : (w.runCrimp R).IsTT q g := ⟨hq', hg',
        by rw [(R.lohi' hg' hgZ).1]; exact i1, by rw [(R.lohi' hg' hgZ).2]; exact i2⟩
      have := R.cl_tt htt
      rw [hn'] at this
      rw [this]
  · subst hqP
    have hPQ := P_not_mem_Q hn
    rw [nxt_prv R.hA]
    by_cases hgQ : g ∈ R.Q
    · exfalso; have := (Q_bounds hup hk hgQ).1; linarith
    · simp only [psiE, hPQ, hgQ, hAQ, if_true, if_false, Option.some.injEq]
      have hg' := R.mem_C'_of hg hgQ
      have hgZ : g ≠ R.Z := fun e => hgQ (e ▸ hZQ)
      have hP' := R.mem_C'_of hq hPQ
      have htt : (w.runCrimp R).IsTT R.P g := ⟨hP', hg',
        by rw [(R.lohi' hg' hgZ).1]; exact i1, by rw [(R.lohi' hg' hgZ).2]; exact i2⟩
      have := R.cl_tt htt
      rw [R.nxt' hP', if_pos (R.star_even hk).symm] at this
      rw [this]
  · subst hqZ
    have hNQ := nZ_not_mem_Q hn
    by_cases hgQ : g ∈ R.Q
    · exfalso; have := (Q_bounds hup hk hgQ).2; linarith
    · simp only [psiE, hZQ, hgQ, hNQ, if_true, if_false, Option.some.injEq]
      have hg' := R.mem_C'_of hg hgQ
      have hgZ : g ≠ R.Z := fun e => hgQ (e ▸ hZQ)
      have htt : (w.runCrimp R).IsTT R.Z g := ⟨R.Z_mem', hg',
        by rw [(R.lohi' hg' hgZ).1]; exact i1, by rw [(R.lohi' hg' hgZ).2]; exact i2⟩
      have := R.cl_tt htt
      rw [R.nxt' R.Z_mem', if_neg R.Z_ne_star] at this
      rw [this]
  · have h1 := R.t_mem_Q (i := i) (by omega)
    have h2 : nxt w.C (R.t i) ∈ R.Q := by rw [← R.t_succ]; exact R.t_mem_Q (by omega)
    simp only [psiE, h1, h2, if_true]

lemma psiE_tc {q l : ι} (h : w.IsTC q l) {a b : ι} (ha : a = q ∨ a = nxt w.C q)
    (hb : b = l ∨ b = nxt w.C l) : R.psiE a b = R.psiE q l := by
  have hn := R.card_even_ge hk
  obtain ⟨hq, hl, hne, hcq, hup'⟩ := h
  have hP := R.c_prvA hup; have hZ := (R.c_Z hup).1 hk; have al := R.al_pos
  have hPQ := P_not_mem_Q hn; have hNQ := nZ_not_mem_Q hn
  have hAQ : R.A ∈ R.Q := R.t_mem_Q (i := 0) (by omega)
  have hZQ : R.Z ∈ R.Q := R.t_mem_Q le_rfl
  have hPmin : ¬ w.up R.P := by rw [up_prv R.hA]; exact not_not.2 hup
  have cpos : ∀ i ≤ R.k + 1, w.c (R.t i) = w.c R.A ∨ w.c (R.t i) = w.c R.A - R.al :=
    fun i hi => c_t_mem hup hi
  have tc' : ∀ {q l}, q ∈ w.C → q ∉ R.B → l ∈ w.C → l ∉ R.B → q ≠ l → w.c q = w.c l →
      (w.up q ↔ w.up l) → (w.runCrimp R).IsTC q l := by
    intro q l hq hqB hl hlB hne hc hu
    have hq' := R.mem_C'.2 ⟨hq, hqB⟩; have hl' := R.mem_C'.2 ⟨hl, hlB⟩
    exact ⟨hq', hl', hne, hc, by rw [up' hup hq', up' hup hl']; exact hu⟩
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  have runQ : ∀ {i x}, i ≤ R.k + 1 → (x = R.t i ∨ x = nxt w.C (R.t i)) → x ∈ R.Q := by
    intro i x hi hx
    rcases hx with rfl | rfl
    · exact R.t_mem_Q (by omega)
    · rw [← R.t_succ]; exact R.t_mem_Q (by omega)
  have outQ : ∀ {q x}, q ∉ R.Q → nxt w.C q ∉ R.Q → (x = q ∨ x = nxt w.C q) → x ∉ R.Q := by
    intro q x h1 h2 hx; rcases hx with rfl | rfl <;> assumption
  -- `Z` together with the sectors at an outer crease at one end of the run
  have mergedRow : ∀ {q}, q ∈ w.C → q ∉ R.Q → nxt w.C q ∉ R.Q →
      (w.c q = w.c R.A ∨ w.c q = w.c R.A - R.al) → ∀ x, (x = q ∨ x = nxt w.C q) →
      R.cl s(R.Z, x) = R.cl s(R.Z, q) := by
    intro q hq hq1 hq2 hcp x hx
    have nq : nxt (w.runCrimp R).C q = nxt w.C q := by
      rw [R.nxt' (R.mem_C'_of hq hq1), if_neg (ns_of_outer hk hup hq hq2)]
    have hin := in_merged hk hup hcp
    have h' : (w.runCrimp R).IsTT q R.Z := ⟨R.mem_C'_of hq hq1, R.Z_mem', hin.1, hin.2⟩
    rcases hx with rfl | rfl
    · rfl
    · have := R.cl_tt h'; rw [nq] at this; rw [cl_swap, ← this, cl_swap]
  rcases crease_cases hn hq with ⟨hq1, hq2⟩ | hqP | hqZ | ⟨i, hi, rfl⟩ <;>
    rcases crease_cases hn hl with ⟨hl1, hl2⟩ | hlP | hlZ | ⟨j, hj, rfl⟩
  -- outer / outer
  · have htc := tc' hq (notB hq1) hl (notB hl1) hne hcq hup'
    have nq : nxt (w.runCrimp R).C q = nxt w.C q := by
      rw [R.nxt' (R.mem_C'_of hq hq1), if_neg (ns_of_outer hk hup hq hq2)]
    have nl : nxt (w.runCrimp R).C l = nxt w.C l := by
      rw [R.nxt' (R.mem_C'_of hl hl1), if_neg (ns_of_outer hk hup hl hl2)]
    simp only [psiE, outQ hq1 hq2 ha, outQ hl1 hl2 hb, hq1, hl1, if_false, Option.some.injEq]
    rw [R.cl_tc htc (by rw [nq]; exact ha) (by rw [nl]; exact hb)]
  -- outer / P
  · subst hlP
    have htc := tc' hq (notB hq1) (w.prv_mem R.hA) (notB hPQ) hne hcq hup'
    have nq : nxt (w.runCrimp R).C q = nxt w.C q := by
      rw [R.nxt' (R.mem_C'_of hq hq1), if_neg (ns_of_outer hk hup hq hq2)]
    have nl : nxt (w.runCrimp R).C R.P = R.Z := by
      rw [R.nxt' (R.mem_C'_of (w.prv_mem R.hA) hPQ), if_pos (R.star_even hk).symm]
    rw [nxt_prv R.hA] at hb
    rcases hb with rfl | rfl
    · simp only [psiE, outQ hq1 hq2 ha, hq1, hPQ, if_false, Option.some.injEq]
      rw [R.cl_tc htc (by rw [nq]; exact ha) (Or.inl rfl)]
    · simp only [psiE, outQ hq1 hq2 ha, hq1, hPQ, hAQ, if_true, if_false, Option.some.injEq]
      rw [cl_swap, R.cl_tc htc (by rw [nq]; exact ha) (by rw [nl]; right; rfl)]
  -- outer / Z
  · subst hlZ
    have htc := tc' hq (notB hq1) R.Z_mem R.Z_not_mem_B hne hcq hup'
    have nq : nxt (w.runCrimp R).C q = nxt w.C q := by
      rw [R.nxt' (R.mem_C'_of hq hq1), if_neg (ns_of_outer hk hup hq hq2)]
    have nl : nxt (w.runCrimp R).C R.Z = nxt w.C R.Z := by
      rw [R.nxt' R.Z_mem', if_neg R.Z_ne_star]
    rcases hb with rfl | rfl
    · simp only [psiE, outQ hq1 hq2 ha, hq1, hZQ, if_true, if_false, Option.some.injEq]
      rw [cl_swap, R.cl_tc htc (by rw [nq]; exact ha) (Or.inl rfl), cl_swap]
    · simp only [psiE, outQ hq1 hq2 ha, hq1, hZQ, hNQ, if_true, if_false, Option.some.injEq]
      rw [R.cl_tc htc (by rw [nq]; exact ha) (by rw [nl]; right; rfl), cl_swap]
  -- outer / run crease
  · simp only [psiE, outQ hq1 hq2 ha, hq1, runQ hj hb, R.t_mem_Q (i := j) (by omega), if_true,
      if_false, Option.some.injEq]
    exact mergedRow hq hq1 hq2 (by rw [hcq]; exact cpos j hj) a ha
  -- P / outer
  · subst hqP
    have htc := tc' (w.prv_mem R.hA) (notB hPQ) hl (notB hl1) hne hcq hup'
    have nl : nxt (w.runCrimp R).C l = nxt w.C l := by
      rw [R.nxt' (R.mem_C'_of hl hl1), if_neg (ns_of_outer hk hup hl hl2)]
    have nq : nxt (w.runCrimp R).C R.P = R.Z := by
      rw [R.nxt' (R.mem_C'_of (w.prv_mem R.hA) hPQ), if_pos (R.star_even hk).symm]
    rw [nxt_prv R.hA] at ha
    rcases ha with rfl | rfl
    · simp only [psiE, outQ hl1 hl2 hb, hPQ, hl1, if_false, Option.some.injEq]
      rw [R.cl_tc htc (Or.inl rfl) (by rw [nl]; exact hb)]
    · simp only [psiE, outQ hl1 hl2 hb, hPQ, hl1, hAQ, if_true, if_false, Option.some.injEq]
      rw [R.cl_tc htc (by rw [nq]; right; rfl) (by rw [nl]; exact hb)]
  -- P / P
  · exact absurd (hqP.trans hlP.symm) hne
  -- P / Z: opposite types
  · exfalso; subst hqP; subst hlZ; exact hPmin (hup'.2 hZ.2)
  -- P / run: positions
  · exfalso; subst hqP; rcases cpos j hj with e | e <;> rw [e] at hcq <;> linarith
  -- Z / outer
  · subst hqZ
    have htc := tc' R.Z_mem R.Z_not_mem_B hl (notB hl1) hne hcq hup'
    have nl : nxt (w.runCrimp R).C l = nxt w.C l := by
      rw [R.nxt' (R.mem_C'_of hl hl1), if_neg (ns_of_outer hk hup hl hl2)]
    have nq : nxt (w.runCrimp R).C R.Z = nxt w.C R.Z := by
      rw [R.nxt' R.Z_mem', if_neg R.Z_ne_star]
    rcases ha with rfl | rfl
    · simp only [psiE, outQ hl1 hl2 hb, hZQ, hl1, if_true, if_false, Option.some.injEq]
      rw [R.cl_tc htc (Or.inl rfl) (by rw [nl]; exact hb)]
    · simp only [psiE, outQ hl1 hl2 hb, hZQ, hNQ, hl1, if_true, if_false, Option.some.injEq]
      rw [R.cl_tc htc (by rw [nq]; right; rfl) (by rw [nl]; exact hb)]
  -- Z / P
  · exfalso; subst hqZ; subst hlP; exact hPmin (hup'.1 hZ.2)
  -- Z / Z
  · exact absurd (hqZ.trans hlZ.symm) hne
  -- Z / run
  · exfalso; subst hqZ; rcases cpos j hj with e | e <;> rw [e] at hcq <;> linarith [hZ.1]
  -- run / outer
  · simp only [psiE, outQ hl1 hl2 hb, hl1, runQ hi ha, R.t_mem_Q (i := i) (by omega), if_true,
      if_false, Option.some.injEq]
    exact mergedRow hl hl1 hl2 (by rw [← hcq]; exact cpos i hi) b hb
  -- run / P, run / Z: positions
  · exfalso; subst hlP; rcases cpos i hi with e | e <;> rw [e] at hcq <;> linarith
  · exfalso; subst hlZ; rcases cpos i hi with e | e <;> rw [e] at hcq <;> linarith [hZ.1]
  -- run / run
  · simp only [psiE, runQ hi ha, runQ hj hb, R.t_mem_Q (i := i) (by omega),
      R.t_mem_Q (i := j) (by omega), if_true]

/-- `ψ` on unordered pairs. -/
def PsiE : Sym2 ι → Option (Quot (w.runCrimp R).Linked) := Sym2.lift ⟨R.psiE, R.psiE_symm⟩

/-- **(1)** All the vertices of a row of `w` have the same image under `ψ`. -/
lemma PsiE_row {r : Row ι} (hr : r ∈ w.rows) {u v : Sym2 ι} (hu : u ∈ r.verts)
    (hv : v ∈ r.verts) : R.PsiE u = R.PsiE v := by
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, hqg, rfl⟩ := mem_ttRows.1 hr
    rw [Row.mem_verts_tt] at hu hv
    have e := psiE_tt hk hup hqg
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simp only [PsiE, Sym2.lift_mk] <;> first | rfl | exact e | exact e.symm
  · obtain ⟨q, l, -, hql, rfl⟩ := mem_tcRows.1 hr
    have key : ∀ x ∈ (Row.tc q (nxt w.C q) l (nxt w.C l)).verts, R.PsiE x = R.psiE q l := by
      intro x hx
      rw [Row.mem_verts_tc] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp only [PsiE, Sym2.lift_mk] <;>
        first
        | exact psiE_tc hk hup hql (Or.inr rfl) (Or.inl rfl)
        | exact psiE_tc hk hup hql (Or.inl rfl) (Or.inr rfl)
        | exact psiE_tc hk hup hql (Or.inr rfl) (Or.inr rfl)
    rw [key u hu, key v hv]

lemma PsiE_conn {u v : Sym2 ι} (h : w.Conn u v) : R.PsiE u = R.PsiE v := by
  induction h with
  | rel u v h => obtain ⟨r, hr, hu, hv⟩ := h; exact PsiE_row hk hup hr hu hv
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- **(3)** The adjacent pairs of the deleted creases go to `β`. -/
lemma PsiE_adj_B {j : ι} (hj : j ∈ R.B) : R.PsiE (w.adj j) = none := by
  obtain ⟨i, -, hi, rfl⟩ := R.mem_B.1 hj
  have h1 := R.t_mem_Q (i := i) (by omega)
  have h2 : nxt w.C (R.t i) ∈ R.Q := by rw [← R.t_succ]; exact R.t_mem_Q (by omega)
  simp only [PsiE, adj, Sym2.lift_mk, psiE, h1, h2, if_true]

/-- **(3)** The adjacent pair of a surviving crease goes to the component of its adjacent
pair in `w'`. -/
lemma PsiE_adj {j : ι} (hj : j ∈ w.C) (hjB : j ∉ R.B) :
    R.PsiE (w.adj j) = some (R.cl ((w.runCrimp R).adj j)) := by
  have hn := R.card_even_ge hk
  have hj' := R.mem_C'.2 ⟨hj, hjB⟩
  have hAQ : R.A ∈ R.Q := R.t_mem_Q (i := 0) (by omega)
  have hZQ : R.Z ∈ R.Q := R.t_mem_Q le_rfl
  unfold adj
  rw [R.nxt' hj']
  rcases crease_cases hn hj with ⟨h1, h2⟩ | hjP | hjZ | ⟨i, hi, rfl⟩
  · rw [if_neg (ns_of_outer hk hup hj h2)]
    simp only [PsiE, Sym2.lift_mk, psiE, h1, h2, if_false]
  · subst hjP
    rw [if_pos (R.star_even hk).symm, nxt_prv R.hA]
    simp only [PsiE, Sym2.lift_mk, psiE, P_not_mem_Q hn, hAQ, if_true, if_false,
      Option.some.injEq]
    exact cl_swap R _ _
  · subst hjZ
    rw [if_neg R.Z_ne_star]
    simp only [PsiE, Sym2.lift_mk, psiE, hZQ, nZ_not_mem_Q hn, if_true, if_false]
  · exact absurd (R.t_mem_B (by simp [hk]) hi) hjB

/-- **Lemma 4, `k` even, `A` a maximum.** -/
theorem lemma6_even_up {j j' : ι} (hj : j ∈ w.C) (hj' : j' ∈ w.C) (h : w.SameComp j j') :
    (j ∈ R.B ↔ j' ∈ R.B) ∧ (j ∉ R.B → (w.runCrimp R).SameComp j j') := by
  have e := PsiE_conn hk hup h
  by_cases hjB : j ∈ R.B <;> by_cases hjB' : j' ∈ R.B
  · exact ⟨iff_of_true hjB hjB', fun h => absurd hjB h⟩
  · rw [PsiE_adj_B hk hup hjB, PsiE_adj hk hup hj' hjB'] at e; exact absurd e (by simp)
  · rw [PsiE_adj hk hup hj hjB, PsiE_adj_B hk hup hjB'] at e; exact absurd e (by simp)
  · rw [PsiE_adj hk hup hj hjB, PsiE_adj hk hup hj' hjB', Option.some.injEq] at e
    exact ⟨iff_of_false hjB hjB', fun _ => Quot.eqvGen_exact e⟩

end even

end RunData

/-- **Lemma 4, `k` even.**  Crimping a run of an odd number of sectors isolates the adjacent
pairs of its creases, and merges no two components of the rest. -/
theorem lemma6_even (R : w.RunData) (hk : Even R.k) {j j' : ι} (hj : j ∈ w.C) (hj' : j' ∈ w.C)
    (h : w.SameComp j j') :
    (j ∈ R.B ↔ j' ∈ R.B) ∧ (j ∉ R.B → (w.runCrimp R).SameComp j j') := by
  by_cases hup : w.up R.A
  · exact RunData.lemma6_even_up hk hup hj hj' h
  · have hup' : w.refl.up R.refl'.A := (refl_up R.hA).2 hup
    have h' : w.refl.SameComp j j' := by rw [refl_sameComp]; exact h
    have := RunData.lemma6_even_up (R := R.refl') hk hup' hj hj' h'
    rw [← refl_runCrimp, refl_sameComp, RunData.refl'_B] at this
    exact this


/-! #### `k` odd -/

namespace RunData

variable (R : w.RunData)

/-- The outer sector `g` reaches the upper end `h = c A` of the run. -/
def Reach (g : ι) : Prop := w.lo g < w.c R.A ∧ w.c R.A ≤ w.hi g

instance (g : ι) : Decidable (R.Reach g) := by unfold Reach; infer_instance

/-- The map `ψ` for `k` odd (Table 1, second column); `none` is "undefined". -/
def psiO (x y : ι) : Option (Quot (w.runCrimp R).Linked) :=
  if x ∈ R.Q ∧ y ∈ R.Q then some (R.cl s(R.A, R.Z))
  else if x ∈ R.B then (if R.Reach y then some (R.cl s(R.A, y)) else none)
  else if y ∈ R.B then (if R.Reach x then some (R.cl s(R.A, x)) else none)
  else some (R.cl s(x, y))

lemma psiO_symm (x y : ι) : R.psiO x y = R.psiO y x := by
  unfold psiO
  by_cases hx : x ∈ R.Q <;> by_cases hy : y ∈ R.Q <;> by_cases bx : x ∈ R.B <;>
    by_cases by' : y ∈ R.B <;>
    simp only [hx, hy, bx, by', and_self, and_true, and_false, true_and, false_and, if_true,
      if_false] <;>
    first
    | rfl
    | exact absurd (R.B_subset_Q bx) hx
    | exact absurd (R.B_subset_Q by') hy
    | rw [cl_swap]

section odd

variable {R} (hk : ¬ Even R.k) (hup : w.up R.A) (hn : R.k + 4 ≤ w.C.card)
include hk hup hn

lemma odd_facts :
    R.A ∈ R.Q ∧ R.Z ∈ R.Q ∧ R.A ∉ R.B ∧ R.Z ∉ R.B ∧ R.star = R.A ∧
      R.P ∉ R.Q ∧ nxt w.C R.Z ∉ R.Q := by
  refine ⟨R.t_mem_Q (i := 0) (by omega), R.t_mem_Q le_rfl, ?_, R.Z_not_mem_B, R.star_odd hk,
    P_not_mem_Q hn, nZ_not_mem_Q hn⟩
  have := R.star_not_mem_B; rwa [R.star_odd hk] at this

/-- Sectors of the run have the interval `[ℓ, h]`. -/
lemma lohi_B {x : ι} (hx : x ∈ R.B) : w.lo x = w.c R.A - R.al ∧ w.hi x = w.c R.A := by
  obtain ⟨i, hi1, hi2, rfl⟩ := R.mem_B.1 hx
  rw [if_neg hk] at hi1
  exact lohi_run hup hi1 hi2

lemma nxt'_A : nxt (w.runCrimp R).C R.A = R.Z := by
  rw [← R.star_odd hk]; exact R.nxt_star

lemma nxt'_out {q : ι} (hq : q ∈ w.C) (hqQ : q ∉ R.Q) :
    nxt (w.runCrimp R).C q = nxt w.C q := by
  rw [R.nxt' (R.mem_C'_of hq hqQ), if_neg]
  rw [R.star_odd hk]; intro e; exact hqQ (e ▸ R.t_mem_Q (i := 0) (by omega))

lemma nxt'_P : nxt (w.runCrimp R).C R.P = R.A := by
  rw [nxt'_out hk hup hn (w.prv_mem R.hA) (P_not_mem_Q hn), nxt_prv R.hA]

lemma nxt'_Z : nxt (w.runCrimp R).C R.Z = nxt w.C R.Z := by
  rw [R.nxt' R.Z_mem', if_neg R.Z_ne_star]

lemma A_mem' : R.A ∈ (w.runCrimp R).C := by
  have := R.star_mem'; rwa [R.star_odd hk] at this

/-- Intervals in `w'` of the sectors outside the run are unchanged. -/
lemma lohi'_odd {g : ι} (hg : g ∈ w.C) (hgB : g ∉ R.B) :
    (w.runCrimp R).lo g = w.lo g ∧ (w.runCrimp R).hi g = w.hi g := by
  by_cases hgZ : g = R.Z
  · subst hgZ; exact lohi'_Z_odd hup hk
  · exact R.lohi' (R.mem_C'.2 ⟨hg, hgB⟩) hgZ

/-- An outer sector reaching `h` sees `f_A` and `f_Z` in one component of `H_{w'}`. -/
lemma reach_cl {g : ι} (hg : g ∈ w.C) (hgQ : g ∉ R.Q) (hr : R.Reach g) :
    R.cl s(R.A, g) = R.cl s(R.Z, g) := by
  obtain ⟨hA, -, -, -, -, -, -⟩ := odd_facts hk hup hn
  have hgB : g ∉ R.B := fun h => hgQ (R.B_subset_Q h)
  have hg' := R.mem_C'.2 ⟨hg, hgB⟩
  obtain ⟨r1, r2⟩ := hr
  rcases lt_or_eq_of_le r2 with r2 | r2
  · -- `h` is interior to `I_g`: the taco–tortilla row `(e_⋆, f_g)` of `w'`
    have htt : (w.runCrimp R).IsTT R.A g := ⟨A_mem' hk hup hn, hg',
      by rw [(lohi'_odd hk hup hn hg hgB).1]; exact r1,
      by rw [(lohi'_odd hk hup hn hg hgB).2]; exact r2⟩
    have := R.cl_tt htt
    rw [nxt'_A hk hup hn] at this
    exact this
  · -- `h` is the upper end of `I_g`: the taco–taco row of `e_⋆` and the upper crease of `g`
    have hu := uc_mem hg
    have hcu : w.c (w.uc g) = w.c R.A := by rw [c_uc hg]; exact r2.symm
    have hgu := mem_sectors_uc hg
    have hA1 : nxt w.C R.A ∈ R.Q := R.t_mem_Q (i := 1) (by omega)
    have hneA : w.uc g ≠ R.A := by
      intro e; rw [e] at hgu
      rcases hgu with h | h
      · exact hgQ (h ▸ hA)
      · exact hgQ (h ▸ hA1)
    have huB : w.uc g ∉ R.B := by
      intro hb
      obtain ⟨i, hi1, hi2, e⟩ := R.mem_B.1 hb
      rw [e] at hgu
      rcases hgu with h | h
      · exact hgQ (h ▸ R.t_mem_Q (by omega))
      · exact hgQ (h ▸ (by rw [← R.t_succ]; exact R.t_mem_Q (by omega)))
    have hu' := R.mem_C'.2 ⟨hu, huB⟩
    have htc : (w.runCrimp R).IsTC (w.uc g) R.A := ⟨hu', A_mem' hk hup hn, hneA, hcu,
      by rw [up' hup hu', up' hup (A_mem' hk hup hn)]; exact iff_of_true (up_uc hg) hup⟩
    have hnu : nxt (w.runCrimp R).C (w.uc g) = nxt w.C (w.uc g) := by
      rw [R.nxt' hu', if_neg (by rw [R.star_odd hk]; exact hneA)]
    have e1 := R.cl_tc htc (a := g) (b := R.A) (by rw [hnu]; exact hgu) (Or.inl rfl)
    have e2 := R.cl_tc htc (a := g) (b := R.Z) (by rw [hnu]; exact hgu)
      (by rw [nxt'_A hk hup hn]; right; rfl)
    rw [cl_swap, e1, ← e2, cl_swap]

/-- A sector ending at a point strictly inside the run and going up reaches `h`; one going
down does not. -/
lemma reach_of_lo {g : ι} (hg : g ∈ w.C) (h1 : w.c R.A - R.al ≤ w.lo g) (h2 : w.lo g < w.c R.A) :
    R.Reach g := by
  have := R.hmin g hg
  have e : w.len g = w.hi g - w.lo g := rfl
  exact ⟨h2, by linarith⟩

lemma not_reach_of_hi {g : ι} (h2 : w.hi g < w.c R.A) : ¬ R.Reach g := fun h => by
  have := h.2; linarith

end odd

end RunData

lemma isTC_comm {q l : ι} (h : w.IsTC q l) : w.IsTC l q :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

/-- The end at a crease `q` of either sector at `q`. -/
lemma end_at {q a : ι} (hq : q ∈ w.C) (ha : a = q ∨ a = nxt w.C q) :
    (w.up q → w.hi a = w.c q) ∧ (¬ w.up q → w.lo a = w.c q) := by
  rcases ha with rfl | rfl
  · exact ⟨fun h => (lo_hi_of_up h).2, fun h => (lo_hi_of_not_up hq h).1⟩
  · have hn := w.nxt_mem hq
    have e := up_nxt hq
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' : ¬ w.up (nxt w.C q) := fun h'' => e.1 h'' h
      rw [(lo_hi_of_not_up hn h').2, prv_nxt hq]
    · have h' : w.up (nxt w.C q) := e.2 h
      rw [(lo_hi_of_up h').1, prv_nxt hq]

namespace RunData

section odd2

variable {R : w.RunData} (hk : ¬ Even R.k) (hup : w.up R.A) (hn : R.k + 4 ≤ w.C.card)
include hk hup hn

lemma psiO_tt {q g : ι} (h : w.IsTT q g) : R.psiO q g = R.psiO (nxt w.C q) g := by
  obtain ⟨hAQ, hZQ, hAB, hZB, hstar, hPQ, hNQ⟩ := odd_facts hk hup hn
  obtain ⟨d1, d2⟩ := tt_distinct h
  obtain ⟨hq, hg, i1, i2⟩ := h
  have hP := R.c_prvA hup; have hZ := ((R.c_Z hup).2 hk).1; have al := R.al_pos
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  -- the general taco–tortilla row of `w'` with an outer or boundary taco
  have row' : ∀ {q g}, q ∈ w.C → q ∉ R.B → g ∈ w.C → g ∉ R.B → w.lo g < w.c q →
      w.c q < w.hi g → R.cl s(q, g) = R.cl s(nxt (w.runCrimp R).C q, g) := by
    intro q g hq hqB hg hgB i1 i2
    exact R.cl_tt ⟨R.mem_C'.2 ⟨hq, hqB⟩, R.mem_C'.2 ⟨hg, hgB⟩,
      by rw [(lohi'_odd hk hup hn hg hgB).1]; exact i1,
      by rw [(lohi'_odd hk hup hn hg hgB).2]; exact i2⟩
  rcases crease_cases hn hq with ⟨hq1, hq2⟩ | hqP | hqZ | ⟨i, hi, rfl⟩
  · have hn' := nxt'_out hk hup hn hq hq1
    by_cases hgB : g ∈ R.B
    · obtain ⟨l1, l2⟩ := lohi_B hk hup hn hgB
      simp only [psiO, hq1, hq2, notB hq1, notB hq2, hgB, false_and, if_false, if_true]
      have e := end_at hq (Or.inl rfl)
      have e' := end_at hq (Or.inr rfl)
      by_cases hu : w.up q
      · rw [if_neg (not_reach_of_hi hk hup hn (by rw [e.1 hu]; linarith)),
          if_neg (not_reach_of_hi hk hup hn (by rw [e'.1 hu]; linarith))]
      · rw [if_pos (reach_of_lo hk hup hn hq (by rw [e.2 hu]; linarith) (by rw [e.2 hu]; linarith)),
          if_pos (reach_of_lo hk hup hn (w.nxt_mem hq) (by rw [e'.2 hu]; linarith)
            (by rw [e'.2 hu]; linarith))]
        obtain ⟨a1, a2⟩ := lohi_A hup
        have := row' hq (notB hq1) R.hA hAB (by rw [a1]; linarith) (by rw [a2]; linarith)
        rw [hn'] at this
        rw [cl_swap, this, cl_swap]
    · have e1 : R.psiO q g = some (R.cl s(q, g)) := by
        simp only [psiO, hq1, notB hq1, hgB, false_and, if_false]
      have e2 : R.psiO (nxt w.C q) g = some (R.cl s(nxt w.C q, g)) := by
        simp only [psiO, hq2, notB hq2, hgB, false_and, if_false]
      rw [e1, e2, row' hq (notB hq1) hg hgB i1 i2, hn']
  · subst hqP
    rw [nxt_prv R.hA] at d2 ⊢
    by_cases hgB : g ∈ R.B
    · exfalso; have := (lohi_B hk hup hn hgB).1; linarith
    · have e1 : R.psiO R.P g = some (R.cl s(R.P, g)) := by
        simp only [psiO, hPQ, notB hPQ, hgB, false_and, if_false]
      have e2 : R.psiO R.A g = some (R.cl s(R.A, g)) := by
        by_cases hgQ : g ∈ R.Q
        · have hgZ : g = R.Z := by
            obtain ⟨j, hj, rfl⟩ := R.mem_Q.1 hgQ
            rcases Nat.eq_zero_or_pos j with h0 | hpos
            · exact absurd (by rw [h0]; rfl) d2
            · by_cases hjZ : j = R.k + 2
              · rw [hjZ]
              · exact absurd (R.t_mem_B (by rw [if_neg hk]; omega) (by omega)) hgB
          subst hgZ
          simp only [psiO, hAQ, hZQ, and_self, if_true]
        · simp only [psiO, hgQ, hAB, hgB, and_false, if_false]
      rw [e1, e2, row' hq (notB hPQ) hg hgB i1 i2, nxt'_P hk hup hn]
  · subst hqZ
    by_cases hgB : g ∈ R.B
    · exfalso; have := (lohi_B hk hup hn hgB).1; linarith
    · have e1 : R.psiO R.Z g = some (R.cl s(R.Z, g)) := by
        by_cases hgQ : g ∈ R.Q
        · have hgA : g = R.A := by
            obtain ⟨j, hj, rfl⟩ := R.mem_Q.1 hgQ
            by_cases hjZ : j = R.k + 2
            · exact absurd (by rw [hjZ]) d1
            · rcases Nat.eq_zero_or_pos j with h0 | hpos
              · rw [h0]; rfl
              · exact absurd (R.t_mem_B (by rw [if_neg hk]; omega) (by omega)) hgB
          subst hgA
          simp only [psiO, hAQ, hZQ, and_self, if_true, Option.some.injEq]
          exact cl_swap R _ _
        · simp only [psiO, hgQ, hZB, hgB, and_false, if_false]
      have e2 : R.psiO (nxt w.C R.Z) g = some (R.cl s(nxt w.C R.Z, g)) := by
        simp only [psiO, hNQ, notB hNQ, hgB, false_and, if_false]
      rw [e1, e2, row' R.Z_mem hZB hg hgB i1 i2, nxt'_Z hk hup hn]
  · have h1 := R.t_mem_Q (i := i) (by omega)
    have h2 : nxt w.C (R.t i) ∈ R.Q := by rw [← R.t_succ]; exact R.t_mem_Q (by omega)
    by_cases hgQ : g ∈ R.Q
    · simp only [psiO, h1, h2, hgQ, and_self, if_true]
    · have hgB := notB hgQ
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · -- the crease `A` at `h`
        subst h0
        have hr : R.Reach g := ⟨i1, i2.le⟩
        have hB1 : nxt w.C (R.t 0) ∈ R.B := by
          rw [← R.t_succ]; exact R.t_mem_B (by rw [if_neg hk]) (by omega)
        simp only [psiO, hgQ, and_false, if_false, hB1, hr, if_true]
        show (if R.A ∈ R.B then _ else if g ∈ R.B then _ else some (R.cl s(R.A, g))) = _
        rw [if_neg hAB, if_neg hgB]
      · have hiB : R.t i ∈ R.B := R.t_mem_B (by rw [if_neg hk]; omega) (by omega)
        by_cases hik : i = R.k + 1
        · -- the crease `t (k+1)` at `h`, between the run and `f_Z`
          subst hik
          have hc : w.c (R.t (R.k + 1)) = w.c R.A := by
            rw [c_t hup le_rfl, if_pos (by rw [Nat.even_add_one]; exact hk)]
          have hr : R.Reach g := ⟨by rw [← hc]; exact i1, by rw [← hc]; exact i2.le⟩
          rw [← R.t_succ]
          simp only [psiO, hgQ, and_false, if_false, hiB, hr, if_true, hZB, hgB]
          rw [reach_cl hk hup hn hg hgQ hr]
        · have hiB' : nxt w.C (R.t i) ∈ R.B := by
            rw [← R.t_succ]; exact R.t_mem_B (by rw [if_neg hk]; omega) (by omega)
          simp only [psiO, hgQ, and_false, if_false, hiB, hiB', if_true]

/-- Away from the run, `ψ` is the identity on pairs of distinct sectors. -/
lemma psiO_plain {a b : ι} (ha : a ∉ R.B) (hb : b ∉ R.B) (hab : a ≠ b) :
    R.psiO a b = some (R.cl s(a, b)) := by
  obtain ⟨hAQ, hZQ, hAB, hZB, -, -, -⟩ := odd_facts hk hup hn
  by_cases h : a ∈ R.Q ∧ b ∈ R.Q
  · -- then `{a, b} = {A, Z}`
    have key : ∀ x ∈ R.Q, x ∉ R.B → x = R.A ∨ x = R.Z := by
      intro x hx hxB
      obtain ⟨j, hj, rfl⟩ := R.mem_Q.1 hx
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · left; rw [h0]; rfl
      · by_cases hjZ : j = R.k + 2
        · right; rw [hjZ]
        · exact absurd (R.t_mem_B (by rw [if_neg hk]; omega) (by omega)) hxB
    simp only [psiO, h, and_self, if_true, Option.some.injEq]
    rcases key a h.1 ha with rfl | rfl <;> rcases key b h.2 hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact cl_swap R _ _
    · exact absurd rfl hab
  · simp only [psiO, h, ha, hb, if_false]

/-- A pair of an outer sector and a run sector. -/
lemma psiO_runR {a b : ι} (ha : a ∉ R.Q) (hb : b ∈ R.B) :
    R.psiO a b = if R.Reach a then some (R.cl s(R.A, a)) else none := by
  have haB : a ∉ R.B := fun h => ha (R.B_subset_Q h)
  simp only [psiO, ha, false_and, haB, hb, if_false, if_true]

lemma tc'_odd {q l : ι} (hq : q ∈ w.C) (hqB : q ∉ R.B) (hl : l ∈ w.C) (hlB : l ∉ R.B)
    (hne : q ≠ l) (hc : w.c q = w.c l) (hu : w.up q ↔ w.up l) : (w.runCrimp R).IsTC q l := by
  have hq' := R.mem_C'.2 ⟨hq, hqB⟩; have hl' := R.mem_C'.2 ⟨hl, hlB⟩
  exact ⟨hq', hl', hne, hc, by rw [up' hup hq', up' hup hl']; exact hu⟩

lemma H_OO {q l a b : ι} (h : w.IsTC q l) (hq1 : q ∉ R.Q) (hq2 : nxt w.C q ∉ R.Q)
    (hl1 : l ∉ R.Q) (hl2 : nxt w.C l ∉ R.Q) (ha : a = q ∨ a = nxt w.C q)
    (hb : b = l ∨ b = nxt w.C l) : R.psiO a b = R.psiO q l := by
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  obtain ⟨hq, hl, hne, hc, hu⟩ := h
  have htc := tc'_odd hk hup hn hq (notB hq1) hl (notB hl1) hne hc hu
  obtain ⟨-, d2, d3, d4⟩ := tc_distinct (w := w) ⟨hq, hl, hne, hc, hu⟩
  have haB : a ∉ R.B := by rcases ha with rfl | rfl <;> exact notB ‹_›
  have hbB : b ∉ R.B := by rcases hb with rfl | rfl <;> exact notB ‹_›
  have hab : a ≠ b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
  rw [psiO_plain hk hup hn haB hbB hab, psiO_plain hk hup hn (notB hq1) (notB hl1) hne,
    R.cl_tc htc (by rw [nxt'_out hk hup hn hq hq1]; exact ha)
      (by rw [nxt'_out hk hup hn hl hl1]; exact hb)]

lemma H_OP {q a b : ι} (h : w.IsTC q R.P) (hq1 : q ∉ R.Q) (hq2 : nxt w.C q ∉ R.Q)
    (ha : a = q ∨ a = nxt w.C q) (hb : b = R.P ∨ b = nxt w.C R.P) :
    R.psiO a b = R.psiO q R.P := by
  obtain ⟨hAQ, hZQ, hAB, hZB, -, hPQ, -⟩ := odd_facts hk hup hn
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  obtain ⟨hq, hl, hne, hc, hu⟩ := h
  have htc := tc'_odd hk hup hn hq (notB hq1) hl (notB hPQ) hne hc hu
  obtain ⟨-, d2, d3, d4⟩ := tc_distinct (w := w) ⟨hq, hl, hne, hc, hu⟩
  rw [nxt_prv R.hA] at hb d2 d4
  have haB : a ∉ R.B := by rcases ha with rfl | rfl <;> exact notB ‹_›
  have hbB : b ∉ R.B := by rcases hb with rfl | rfl <;> [exact notB hPQ; exact hAB]
  have hab : a ≠ b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
  rw [psiO_plain hk hup hn haB hbB hab, psiO_plain hk hup hn (notB hq1) (notB hPQ) hne,
    R.cl_tc htc (by rw [nxt'_out hk hup hn hq hq1]; exact ha)
      (by rw [nxt'_P hk hup hn]; exact hb)]

lemma H_OZ {q a b : ι} (h : w.IsTC q R.Z) (hq1 : q ∉ R.Q) (hq2 : nxt w.C q ∉ R.Q)
    (ha : a = q ∨ a = nxt w.C q) (hb : b = R.Z ∨ b = nxt w.C R.Z) :
    R.psiO a b = R.psiO q R.Z := by
  obtain ⟨hAQ, hZQ, hAB, hZB, -, hPQ, hNQ⟩ := odd_facts hk hup hn
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  obtain ⟨hq, hl, hne, hc, hu⟩ := h
  have htc := tc'_odd hk hup hn hq (notB hq1) hl hZB hne hc hu
  obtain ⟨-, d2, d3, d4⟩ := tc_distinct (w := w) ⟨hq, hl, hne, hc, hu⟩
  have haB : a ∉ R.B := by rcases ha with rfl | rfl <;> exact notB ‹_›
  have hbB : b ∉ R.B := by rcases hb with rfl | rfl <;> [exact hZB; exact notB hNQ]
  have hab : a ≠ b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
  rw [psiO_plain hk hup hn haB hbB hab, psiO_plain hk hup hn (notB hq1) hZB hne,
    R.cl_tc htc (by rw [nxt'_out hk hup hn hq hq1]; exact ha)
      (by rw [nxt'_Z hk hup hn]; exact hb)]

lemma H_OR {q a b : ι} {j : ℕ} (hj : j ≤ R.k + 1) (h : w.IsTC q (R.t j)) (hq1 : q ∉ R.Q)
    (hq2 : nxt w.C q ∉ R.Q) (ha : a = q ∨ a = nxt w.C q)
    (hb : b = R.t j ∨ b = nxt w.C (R.t j)) : R.psiO a b = R.psiO q (R.t j) := by
  obtain ⟨hAQ, hZQ, hAB, hZB, -, hPQ, hNQ⟩ := odd_facts hk hup hn
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  obtain ⟨hq, hl, hne, hc, hu⟩ := h
  have hP := R.c_prvA hup; have al := R.al_pos
  have haQ : a ∉ R.Q := by rcases ha with rfl | rfl <;> assumption
  have haB := notB haQ
  have haC : a ∈ w.C := by rcases ha with rfl | rfl <;> [exact hq; exact w.nxt_mem hq]
  have hqA : q ≠ R.A := fun e => hq1 (e ▸ hAQ)
  have endq := end_at hq ha
  have endq' := end_at hq (Or.inl rfl)
  obtain ⟨a1, a2⟩ := lohi_A hup
  have hq' := R.mem_C'.2 ⟨hq, notB hq1⟩
  have hnq := nxt'_out hk hup hn hq hq1
  -- the crease `q` is at `h` (and a maximum) or at `ℓ` (and a minimum)
  have hct := c_t hup hj
  have hut := up_t hup hj
  by_cases he : Even j
  · rw [if_pos he] at hct
    have huq : w.up q := hu.2 (hut.2 he)
    have hcq : w.c q = w.c R.A := hc.trans hct
    have hra : ∀ x, (x = q ∨ x = nxt w.C q) → R.Reach x := fun x hx => by
      have := (end_at hq hx).1 huq
      have hlt := lo_lt_hi (w := w) (show x ∈ w.C by
        rcases hx with rfl | rfl <;> [exact hq; exact w.nxt_mem hq])
      exact ⟨by rw [← hcq, ← this]; exact hlt, by rw [← hcq, ← this]⟩
    -- the taco–taco row of `q` and `e_⋆` in `w'`
    have htc : (w.runCrimp R).IsTC q R.A := tc'_odd hk hup hn hq (notB hq1) R.hA hAB hqA hcq
      (iff_of_true huq hup)
    have clA : ∀ x, (x = q ∨ x = nxt w.C q) → R.cl s(R.A, x) = R.cl s(R.A, q) := by
      intro x hx
      rw [cl_swap, R.cl_tc htc (b := R.A) (by rw [hnq]; exact hx) (Or.inl rfl), cl_swap]
    -- the image of the row
    have val : ∀ x y, (x = q ∨ x = nxt w.C q) → (y = R.t j ∨ y = nxt w.C (R.t j)) →
        R.psiO x y = some (R.cl s(R.A, q)) := by
      intro x y hx hy
      have hxQ : x ∉ R.Q := by rcases hx with rfl | rfl <;> assumption
      have hxB := notB hxQ
      have hxC : x ∈ w.C := by rcases hx with rfl | rfl <;> [exact hq; exact w.nxt_mem hq]
      by_cases hyB : y ∈ R.B
      · rw [psiO_runR hk hup hn hxQ hyB, if_pos (hra x hx), clA x hx]
      · -- `y = A` (when `j = 0`) or `y = Z` (when `j = k + 1`)
        have hy' : y = R.A ∨ y = R.Z := by
          rcases hy with rfl | rfl
          · rcases Nat.eq_zero_or_pos j with h0 | hpos
            · left; rw [h0]; rfl
            · exact absurd (R.t_mem_B (by rw [if_neg hk]; omega) hj) hyB
          · rw [← R.t_succ] at hyB ⊢
            by_cases hjk : j = R.k + 1
            · right; rw [hjk]
            · exact absurd (R.t_mem_B (by rw [if_neg hk]; omega) (by omega)) hyB
        have hxy : x ≠ y := fun e => hxQ (e ▸ (by rcases hy' with rfl | rfl <;> assumption))
        rw [psiO_plain hk hup hn hxB hyB hxy, Option.some.injEq]
        rcases hy' with rfl | rfl
        · rw [cl_swap, clA x hx]
        · rw [cl_swap, ← reach_cl hk hup hn hxC hxQ (hra x hx), clA x hx]
    rw [val a b ha hb, val q (R.t j) (Or.inl rfl) (Or.inl rfl)]
  · rw [if_neg he] at hct
    have hpos : 1 ≤ j := by rcases Nat.eq_zero_or_pos j with h0 | h0 <;> [simp [h0] at he; omega]
    have huq : ¬ w.up q := fun h => he (hut.1 (hu.1 h))
    have hcq : w.c q = w.c R.A - R.al := hc.trans hct
    have hjB : R.t j ∈ R.B := R.t_mem_B (by rw [if_neg hk]; omega) hj
    have hjB' : nxt w.C (R.t j) ∈ R.B := by
      rw [← R.t_succ]
      exact R.t_mem_B (by rw [if_neg hk]; omega) (by
        by_contra hjk; push_neg at hjk
        have : j = R.k + 1 := by omega
        rw [this] at he; exact he (by rw [Nat.even_add_one]; exact hk))
    have hra : ∀ x, (x = q ∨ x = nxt w.C q) → R.Reach x := fun x hx => by
      have := (end_at hq hx).2 huq
      exact reach_of_lo hk hup hn (show x ∈ w.C by
        rcases hx with rfl | rfl <;> [exact hq; exact w.nxt_mem hq])
        (by rw [this, hcq]) (by rw [this, hcq]; linarith)
    -- the taco–tortilla row of `q` inside `f_A` in `w'`
    have htt : (w.runCrimp R).IsTT q R.A := ⟨hq', A_mem' hk hup hn,
      by rw [(lohi'_odd hk hup hn R.hA hAB).1, a1, runCrimp_c, hcq]; linarith,
      by rw [(lohi'_odd hk hup hn R.hA hAB).2, a2, runCrimp_c, hcq]; linarith⟩
    have clA : ∀ x, (x = q ∨ x = nxt w.C q) → R.cl s(R.A, x) = R.cl s(R.A, q) := by
      intro x hx
      rcases hx with rfl | rfl
      · rfl
      · have := R.cl_tt htt; rw [hnq] at this; rw [cl_swap, ← this, cl_swap]
    have hbB : b ∈ R.B := by rcases hb with rfl | rfl <;> assumption
    rw [psiO_runR hk hup hn haQ hbB, psiO_runR hk hup hn hq1 hjB, if_pos (hra a ha),
      if_pos (hra q (Or.inl rfl)), clA a ha]

lemma H_PZ {a b : ι} (h : w.IsTC R.P R.Z) (ha : a = R.P ∨ a = nxt w.C R.P)
    (hb : b = R.Z ∨ b = nxt w.C R.Z) : R.psiO a b = R.psiO R.P R.Z := by
  obtain ⟨hAQ, hZQ, hAB, hZB, -, hPQ, hNQ⟩ := odd_facts hk hup hn
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  obtain ⟨hq, hl, hne, hc, hu⟩ := h
  have htc := tc'_odd hk hup hn hq (notB hPQ) hl hZB hne hc hu
  obtain ⟨-, d2, d3, d4⟩ := tc_distinct (w := w) ⟨hq, hl, hne, hc, hu⟩
  rw [nxt_prv R.hA] at ha d3 d4
  have haB : a ∉ R.B := by rcases ha with rfl | rfl <;> [exact notB hPQ; exact hAB]
  have hbB : b ∉ R.B := by rcases hb with rfl | rfl <;> [exact hZB; exact notB hNQ]
  have hab : a ≠ b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
  rw [psiO_plain hk hup hn haB hbB hab, psiO_plain hk hup hn (notB hPQ) hZB hne,
    R.cl_tc htc (by rw [nxt'_P hk hup hn]; exact ha) (by rw [nxt'_Z hk hup hn]; exact hb)]

/-- **(1)** All the vertices of a taco–taco row of `w` have the same image under `ψ`. -/
lemma psiO_tc {q l : ι} (h : w.IsTC q l) {a b : ι} (ha : a = q ∨ a = nxt w.C q)
    (hb : b = l ∨ b = nxt w.C l) : R.psiO a b = R.psiO q l := by
  obtain ⟨hAQ, hZQ, hAB, hZB, -, hPQ, hNQ⟩ := odd_facts hk hup hn
  have hP := R.c_prvA hup; have hZ := ((R.c_Z hup).2 hk).1; have al := R.al_pos
  have pos : ∀ j ≤ R.k + 1, w.c (R.t j) = w.c R.A ∨ w.c (R.t j) = w.c R.A - R.al :=
    fun j hj => c_t_mem hup hj
  have hc := h.2.2.2.1
  have hne := h.2.2.1
  have sw : R.psiO a b = R.psiO q l ↔ R.psiO b a = R.psiO l q := by
    rw [psiO_symm, psiO_symm R l]
  rcases crease_cases hn h.1 with ⟨hq1, hq2⟩ | hqP | hqZ | ⟨i, hi, rfl⟩ <;>
    rcases crease_cases hn h.2.1 with ⟨hl1, hl2⟩ | hlP | hlZ | ⟨j, hj, rfl⟩
  · exact H_OO hk hup hn h hq1 hq2 hl1 hl2 ha hb
  · subst hlP; exact H_OP hk hup hn h hq1 hq2 ha hb
  · subst hlZ; exact H_OZ hk hup hn h hq1 hq2 ha hb
  · exact H_OR hk hup hn hj h hq1 hq2 ha hb
  · subst hqP; exact sw.2 (H_OP hk hup hn (isTC_comm h) hl1 hl2 hb ha)
  · exact absurd (hqP.trans hlP.symm) hne
  · subst hqP; subst hlZ; exact H_PZ hk hup hn h ha hb
  · exfalso; subst hqP; rcases pos j hj with e | e <;> rw [e] at hc <;> linarith
  · subst hqZ; exact sw.2 (H_OZ hk hup hn (isTC_comm h) hl1 hl2 hb ha)
  · subst hqZ; subst hlP; exact sw.2 (H_PZ hk hup hn (isTC_comm h) hb ha)
  · exact absurd (hqZ.trans hlZ.symm) hne
  · exfalso; subst hqZ; rcases pos j hj with e | e <;> rw [e] at hc <;> linarith
  · exact sw.2 (H_OR hk hup hn hi (isTC_comm h) hl1 hl2 hb ha)
  · exfalso; subst hlP; rcases pos i hi with e | e <;> rw [e] at hc <;> linarith
  · exfalso; subst hlZ; rcases pos i hi with e | e <;> rw [e] at hc <;> linarith
  · -- both creases in the run: every pair lies in `Q`
    have runQ : ∀ {m x}, m ≤ R.k + 1 → (x = R.t m ∨ x = nxt w.C (R.t m)) → x ∈ R.Q := by
      intro m x hm hx
      rcases hx with rfl | rfl
      · exact R.t_mem_Q (by omega)
      · rw [← R.t_succ]; exact R.t_mem_Q (by omega)
    simp only [psiO, runQ hi ha, runQ hj hb, R.t_mem_Q (i := i) (by omega),
      R.t_mem_Q (i := j) (by omega), and_self, if_true]

/-- `ψ` on unordered pairs, `k` odd. -/
def PsiO (R : w.RunData) : Sym2 ι → Option (Quot (w.runCrimp R).Linked) :=
  Sym2.lift ⟨R.psiO, R.psiO_symm⟩

lemma PsiO_row {r : Row ι} (hr : r ∈ w.rows) {u v : Sym2 ι} (hu : u ∈ r.verts)
    (hv : v ∈ r.verts) : R.PsiO u = R.PsiO v := by
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, hqg, rfl⟩ := mem_ttRows.1 hr
    rw [Row.mem_verts_tt] at hu hv
    have e := psiO_tt hk hup hn hqg
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simp only [PsiO, Sym2.lift_mk] <;> first | rfl | exact e | exact e.symm
  · obtain ⟨q, l, -, hql, rfl⟩ := mem_tcRows.1 hr
    have key : ∀ x ∈ (Row.tc q (nxt w.C q) l (nxt w.C l)).verts, R.PsiO x = R.psiO q l := by
      intro x hx
      rw [Row.mem_verts_tc] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp only [PsiO, Sym2.lift_mk] <;>
        first
        | rfl
        | exact psiO_tc hk hup hn hql (Or.inr rfl) (Or.inl rfl)
        | exact psiO_tc hk hup hn hql (Or.inl rfl) (Or.inr rfl)
        | exact psiO_tc hk hup hn hql (Or.inr rfl) (Or.inr rfl)
    rw [key u hu, key v hv]

lemma PsiO_conn {u v : Sym2 ι} (h : w.Conn u v) : R.PsiO u = R.PsiO v := by
  induction h with
  | rel u v h => obtain ⟨r, hr, hu, hv⟩ := h; exact PsiO_row hk hup hn hr hu hv
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- **(3)** Every adjacent pair goes to the component of the adjacent pair of the same crease
of `w'`, the deleted creases being replaced by `A = e_⋆`. -/
lemma PsiO_adj {j : ι} (hj : j ∈ w.C) :
    R.PsiO (w.adj j) = some (R.cl ((w.runCrimp R).adj (if j ∈ R.B then R.A else j))) := by
  obtain ⟨hAQ, hZQ, hAB, hZB, -, hPQ, hNQ⟩ := odd_facts hk hup hn
  have notB : ∀ {x}, x ∉ R.Q → x ∉ R.B := fun hx h => hx (R.B_subset_Q h)
  unfold adj
  rcases crease_cases hn hj with ⟨h1, h2⟩ | hjP | hjZ | ⟨i, hi, rfl⟩
  · rw [if_neg (notB h1), nxt'_out hk hup hn hj h1]
    simp only [PsiO, Sym2.lift_mk]
    exact psiO_plain hk hup hn (notB h1) (notB h2) (w.nxt_ne hj).symm
  · subst hjP
    rw [if_neg (notB hPQ), nxt'_P hk hup hn]
    simp only [PsiO, Sym2.lift_mk]
    rw [nxt_prv R.hA]
    exact psiO_plain hk hup hn (notB hPQ) hAB (fun e => hPQ (e ▸ hAQ))
  · subst hjZ
    rw [if_neg hZB, nxt'_Z hk hup hn]
    simp only [PsiO, Sym2.lift_mk]
    exact psiO_plain hk hup hn hZB (notB hNQ) (w.nxt_ne hj).symm
  · have h1 := R.t_mem_Q (i := i) (by omega)
    have h2 : nxt w.C (R.t i) ∈ R.Q := by rw [← R.t_succ]; exact R.t_mem_Q (by omega)
    have hred : (if R.t i ∈ R.B then R.A else R.t i) = R.A := by
      split_ifs with hb
      · rfl
      · rcases Nat.eq_zero_or_pos i with h0 | hpos
        · rw [h0]; rfl
        · exact absurd (R.t_mem_B (by rw [if_neg hk]; omega) hi) hb
    rw [hred, nxt'_A hk hup hn]
    simp only [PsiO, Sym2.lift_mk, psiO, h1, h2, and_self, if_true]

/-- **Lemma 4, `k` odd, `A` a maximum, `f_A` and `f_Z` not adjacent.** -/
theorem lemma6_odd_up {j j' : ι} (hj : j ∈ w.C) (hj' : j' ∈ w.C) (h : w.SameComp j j') :
    (w.runCrimp R).SameComp (if j ∈ R.B then R.A else j) (if j' ∈ R.B then R.A else j') := by
  have e := PsiO_conn hk hup hn h
  rw [PsiO_adj hk hup hn hj, PsiO_adj hk hup hn hj', Option.some.injEq] at e
  exact Quot.eqvGen_exact e

end odd2

end RunData

/-- In a walk with two creases, the two adjacent pairs coincide. -/
lemma sameComp_of_two {w : Walk ι α} (h2 : w.C.card = 2) {x y : ι} (hx : x ∈ w.C) (hy : y ∈ w.C) :
    w.SameComp x y := by
  unfold SameComp adj
  by_cases hxy : x = y
  · subst hxy; exact conn_refl _
  · have hC : w.C = {x, y} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
      · rw [h2, Finset.card_pair hxy]
    have other : ∀ z, z ∈ w.C → z ≠ x → z = y := by
      intro z hz hzx
      have : z ∈ ({x, y} : Finset ι) := hC ▸ hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
    have e1 : nxt w.C x = y := other _ (w.nxt_mem hx) (w.nxt_ne hx)
    have e2 : nxt w.C y = x := by
      by_contra hne
      exact w.nxt_ne hy (other _ (w.nxt_mem hy) hne)
    rw [e1, e2, Sym2.eq_swap]
    exact conn_refl _

/-- **Lemma 4, `k` odd.**  Crimping a run of an even number of sectors merges no two
components, once the deleted creases are replaced by the crease `e_⋆ = A`. -/
theorem lemma6_odd (R : w.RunData) (hk : ¬ Even R.k) {j j' : ι} (hj : j ∈ w.C) (hj' : j' ∈ w.C)
    (h : w.SameComp j j') :
    (w.runCrimp R).SameComp (if j ∈ R.B then R.A else j) (if j' ∈ R.B then R.A else j') := by
  have hred : ∀ {x}, x ∈ w.C → (if x ∈ R.B then R.A else x) ∈ (w.runCrimp R).C := by
    intro x hx
    split_ifs with hb
    · have := R.star_mem'; rwa [R.star_odd hk] at this
    · exact R.mem_C'.2 ⟨hx, hb⟩
  by_cases hn : R.k + 4 ≤ w.C.card
  · by_cases hup : w.up R.A
    · exact RunData.lemma6_odd_up hk hup hn hj hj' h
    · have hup' : w.refl.up R.refl'.A := (refl_up R.hA).2 hup
      have h' : w.refl.SameComp j j' := by rw [refl_sameComp]; exact h
      have := RunData.lemma6_odd_up (R := R.refl') hk hup' hn hj hj' h'
      rw [← refl_runCrimp, refl_sameComp, RunData.refl'_B] at this
      exact this
  · -- the crimped walk has two creases
    have h2 : (w.runCrimp R).C.card = 2 := by
      rw [runCrimp_C, Finset.card_sdiff_of_subset R.B_subset, R.card_B, if_neg hk]
      have := R.hcard; omega
    exact sameComp_of_two h2 (hred hj) (hred hj')

end Walk

end Origami
