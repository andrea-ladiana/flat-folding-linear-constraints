import Origami.Rank
import Origami.Examples

/-!
# Example 2: the row graph of the vertex of Example 1

The components of the row graph `R_v` are computed by exploring it (`grow`, `reach`) and by
checking that the four explored sets are closed; both are finite checks done by `decide`.
With Proposition 2 this gives the rank `11` and the `16` solutions of the rows; the `12`
transitive ones are counted on the permutations of the six sectors.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-! ### Exploring the hypergraph of the rows -/

/-- One step of exploration: add every pair that shares a row with a pair of `S`. -/
def grow (w : Walk ι α) (S : Finset (Sym2 ι)) : Finset (Sym2 ι) :=
  S ∪ (w.rows.filter fun r => ∃ u ∈ S, u ∈ r.verts).biUnion Row.verts

/-- `n` steps of exploration. -/
def reach (w : Walk ι α) : ℕ → Finset (Sym2 ι) → Finset (Sym2 ι)
  | 0, S => S
  | n + 1, S => w.reach n (w.grow S)

lemma grow_conn {S : Finset (Sym2 ι)} {v : Sym2 ι} (hv : v ∈ w.grow S) :
    ∃ u ∈ S, w.Conn u v := by
  rcases Finset.mem_union.1 hv with h | h
  · exact ⟨v, h, conn_refl v⟩
  · obtain ⟨r, hr, hvr⟩ := Finset.mem_biUnion.1 h
    obtain ⟨hr, u, hu, hur⟩ := Finset.mem_filter.1 hr
    exact ⟨u, hu, conn_of_linked ⟨r, hr, hur, hvr⟩⟩

lemma reach_conn : ∀ (n : ℕ) {S : Finset (Sym2 ι)} {v : Sym2 ι}, v ∈ w.reach n S →
    ∃ u ∈ S, w.Conn u v
  | 0, _, v, hv => ⟨v, hv, conn_refl v⟩
  | n + 1, _, _, hv => by
    obtain ⟨u, hu, h⟩ := reach_conn n hv
    obtain ⟨u', hu', h'⟩ := grow_conn hu
    exact ⟨u', hu', conn_trans h' h⟩

/-- A set of pairs closed under exploration is a union of components. -/
lemma conn_closed {K : Finset (Sym2 ι)} (hK : w.grow K ⊆ K) {u v : Sym2 ι} (h : w.Conn u v) :
    u ∈ K ↔ v ∈ K := by
  induction h with
  | rel a b h =>
    obtain ⟨r, hr, ha, hb⟩ := h
    constructor
    · intro haK
      exact hK (Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨r, Finset.mem_filter.2 ⟨hr, a, haK, ha⟩, hb⟩))
    · intro hbK
      exact hK (Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨r, Finset.mem_filter.2 ⟨hr, b, hbK, hb⟩, ha⟩))
  | refl => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### The four components -/

/-- The path pairing `e_4` with `e_5`. -/
def K45 : Finset (Sym2 (Fin 6)) := {s(3, 4), s(3, 5), s(4, 5)}
/-- The cycle on `{1,4}, {2,4}, {2,5}, {1,5}`. -/
def Kcyc : Finset (Sym2 (Fin 6)) := {s(0, 3), s(1, 3), s(1, 4), s(0, 4)}
/-- The path pairing `e_2` with `e_3`, through the pairs of the largest sector `f_3`. -/
def K23 : Finset (Sym2 (Fin 6)) := {s(1, 2), s(0, 2), s(2, 5), s(2, 4), s(2, 3)}
/-- The path pairing `e_6` with `e_1`. -/
def K61 : Finset (Sym2 (Fin 6)) := {s(5, 0), s(1, 5), s(0, 1)}

lemma ex1_closed : ex1.grow K45 ⊆ K45 ∧ ex1.grow Kcyc ⊆ Kcyc ∧ ex1.grow K23 ⊆ K23 ∧
    ex1.grow K61 ⊆ K61 := by decide +kernel

lemma ex1_reach : K45 ⊆ ex1.reach 3 {s(3, 4)} ∧ Kcyc ⊆ ex1.reach 3 {s(0, 3)} ∧
    K23 ⊆ ex1.reach 4 {s(1, 2)} ∧ K61 ⊆ ex1.reach 3 {s(0, 1)} := by decide +kernel

lemma ex1_ovPairs : ex1.ovPairs = K45 ∪ Kcyc ∪ K23 ∪ K61 := by
  ext u
  induction u using Sym2.ind with
  | _ a b =>
  rw [mk_mem_ovPairs]
  revert a b
  decide +kernel

lemma conn_of_mem {K : Finset (Sym2 (Fin 6))} {r : Sym2 (Fin 6)} {n : ℕ}
    (hK : K ⊆ ex1.reach n {r}) {u : Sym2 (Fin 6)} (hu : u ∈ K) : ex1.Conn r u := by
  obtain ⟨r', hr', h⟩ := reach_conn n (hK hu)
  rw [Finset.mem_singleton.1 hr'] at h
  exact h

/-! ### Transitive solutions -/

/-- Two permutations inducing the same order are equal. -/
lemma perm_eq_of_lt_iff {n : ℕ} {p q : Equiv.Perm (Fin n)} (h : ∀ a b, p a < p b ↔ q a < q b) :
    p = q := by
  have key : ∀ (p : Equiv.Perm (Fin n)) i,
      ((p i : Fin n) : ℕ) = (Finset.univ.filter fun j => p j < p i).card := by
    intro p i
    rw [show (Finset.univ.filter fun j => p j < p i) =
        (Finset.Iio (p i)).map p.symm.toEmbedding from ?_, Finset.card_map, Fin.card_Iio]
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Iio,
      Equiv.toEmbedding_apply, Equiv.symm_apply_eq, exists_eq_right]
  ext i
  rw [key p i, key q i]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]

/-- The stackings of the six sectors that satisfy the rows. -/
def P12 : Finset (Equiv.Perm (Fin 6)) :=
  Finset.univ.filter fun p => ∀ r ∈ ex1.rows, r.eval (xOf fun i => ((p i : ℕ) : ℤ)) = 0

lemma P12_card : P12.card = 12 := by decide +kernel

/-- **Example 2.**  The row graph of the vertex of Example 1 has fifteen vertices and four
components: three paths, pairing `e_6` with `e_1` and `e_4` with `e_5` (forced opposite) and
`e_2` with `e_3` (forced equal), and one cycle on `{1,4}, {2,4}, {2,5}, {1,5}`, every pair of
which lies in two rows.  Hence (Proposition 2) the rows have rank `11` and `16` solutions,
every one of the `8` flat-foldable assignments is induced by exactly two of them, and `12` of
the solutions are transitive: the stackings of the six sectors that satisfy the rows. -/
theorem example2 :
    ex1.ovPairs.card = 15 ∧ ex1.comps.card = 4 ∧ ex1.gamma = 3 ∧ ex1.cyc = 1 ∧
    (ex1.SameComp 5 0 ∧ ex1.SameComp 3 4 ∧ ex1.SameComp 1 2) ∧
    (∀ σ ∈ ex1.Wlin, ex1.ext0 σ 5 ≠ ex1.ext0 σ 0 ∧ ex1.ext0 σ 3 ≠ ex1.ext0 σ 4 ∧
      ex1.ext0 σ 1 = ex1.ext0 σ 2) ∧
    (∀ u ∈ Kcyc, (ex1.rowsWith u).card = 2) ∧
    Module.finrank (ZMod 2) (LinearMap.range ex1.rowMap) = 11 ∧ ex1.Sol.ncard = 16 ∧
    (∀ σ ∈ ex1.Wflat, {y | y ∈ ex1.Sol ∧ ex1.asg (lay y) = σ}.ncard = 2) ∧
    P12.card = 12 := by
  obtain ⟨c1, c2, c3, c4⟩ := ex1_closed
  obtain ⟨r1, r2, r3, r4⟩ := ex1_reach
  have hg : ex1.Generic := (example1).1
  have hn := generic_noTC hg
  -- the classes of the four representatives
  have cls : ∀ {K : Finset (Sym2 (Fin 6))} {r : Sym2 (Fin 6)} {n : ℕ}, K ⊆ ex1.reach n {r} →
      ∀ u ∈ K, Quot.mk ex1.Linked u = Quot.mk ex1.Linked r := fun hK u hu =>
    (Quot.eqvGen_sound (conn_of_mem hK hu)).symm
  have sep : ∀ {K : Finset (Sym2 (Fin 6))} {r r' : Sym2 (Fin 6)}, ex1.grow K ⊆ K → r ∈ K →
      r' ∉ K → Quot.mk ex1.Linked r ≠ Quot.mk ex1.Linked r' := fun hK hr hr' e =>
    hr' ((conn_closed hK (Quot.eqvGen_exact e)).1 hr)
  set q1 := Quot.mk ex1.Linked s(3, 4)
  set q2 := Quot.mk ex1.Linked s(0, 3)
  set q3 := Quot.mk ex1.Linked s(1, 2)
  set q4 := Quot.mk ex1.Linked s(0, 1)
  have hcomps : ex1.comps = {q1, q2, q3, q4} := by
    ext q
    simp only [comps, ex1_ovPairs, Finset.mem_image, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨u, (((hu | hu) | hu) | hu), rfl⟩
      · exact Or.inl (cls r1 u hu)
      · exact Or.inr (Or.inl (cls r2 u hu))
      · exact Or.inr (Or.inr (Or.inl (cls r3 u hu)))
      · exact Or.inr (Or.inr (Or.inr (cls r4 u hu)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨s(3, 4), Or.inl (Or.inl (Or.inl (by decide))), rfl⟩
      · exact ⟨s(0, 3), Or.inl (Or.inl (Or.inr (by decide))), rfl⟩
      · exact ⟨s(1, 2), Or.inl (Or.inr (by decide)), rfl⟩
      · exact ⟨s(0, 1), Or.inr (by decide), rfl⟩
  have d12 : q1 ≠ q2 := sep c1 (by decide) (by decide)
  have d13 : q1 ≠ q3 := sep c1 (by decide) (by decide)
  have d14 : q1 ≠ q4 := sep c1 (by decide) (by decide)
  have d23 : q2 ≠ q3 := sep c2 (by decide) (by decide)
  have d24 : q2 ≠ q4 := sep c2 (by decide) (by decide)
  have d34 : q3 ≠ q4 := sep c3 (by decide) (by decide)
  have hadj : ex1.adjComps = {q1, q3, q4} := by
    have a0 : Quot.mk ex1.Linked (ex1.adj 0) = q4 := cls r4 _ (by decide)
    have a1 : Quot.mk ex1.Linked (ex1.adj 1) = q3 := cls r3 _ (by decide)
    have a2 : Quot.mk ex1.Linked (ex1.adj 2) = q3 := cls r3 _ (by decide)
    have a3 : Quot.mk ex1.Linked (ex1.adj 3) = q1 := cls r1 _ (by decide)
    have a4 : Quot.mk ex1.Linked (ex1.adj 4) = q1 := cls r1 _ (by decide)
    have a5 : Quot.mk ex1.Linked (ex1.adj 5) = q4 := cls r4 _ (by decide)
    ext q
    simp only [adjComps, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨k, -, rfl⟩
      fin_cases k
      · exact Or.inr (Or.inr a0)
      · exact Or.inr (Or.inl a1)
      · exact Or.inr (Or.inl a2)
      · exact Or.inl a3
      · exact Or.inl a4
      · exact Or.inr (Or.inr a5)
    · rintro (rfl | rfl | rfl)
      · exact ⟨3, Finset.mem_univ _, a3⟩
      · exact ⟨1, Finset.mem_univ _, a1⟩
      · exact ⟨0, Finset.mem_univ _, a0⟩
  have hc4 : ex1.comps.card = 4 := by
    rw [hcomps, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d12, d13, d14⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d23, d24⟩),
      Finset.card_pair d34]
  have hgam : ex1.gamma = 3 := by
    rw [gamma_eq, hadj, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d13, d14⟩),
      Finset.card_pair d34]
  have hcyc : ex1.cyc = 1 := by
    have := card_comps (w := ex1)
    omega
  have hN : ex1.ovPairs.card = 15 := by rw [ex1_ovPairs]; decide
  -- Proposition 2
  obtain ⟨-, hrank, hsol, hfib⟩ := prop1 hn
  -- the pairs of creases
  have same : ∀ {K : Finset (Sym2 (Fin 6))} {r : Sym2 (Fin 6)} {n : ℕ}, K ⊆ ex1.reach n {r} →
      ∀ i j, ex1.adj i ∈ K → ex1.adj j ∈ K → ex1.SameComp i j := fun hK i j hi hj =>
    conn_trans (conn_symm (conn_of_mem hK hi)) (conn_of_mem hK hj)
  have s50 := same r4 5 0 (by decide) (by decide)
  have s34 := same r1 3 4 (by decide) (by decide)
  have s12 := same r3 1 2 (by decide) (by decide)
  have hfl : ex1.asg (xOf fig1) ∈ ex1.Wlin :=
    Wflat_subset_Wlin ⟨fig1, (example1).2.2.2.2.1, rfl⟩
  have rel := (theorem2 hn).2.1
  refine ⟨hN, hc4, hgam, hcyc, ⟨s50, s34, s12⟩, fun σ hσ => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have e := rel 5 (Finset.mem_univ _) 0 (Finset.mem_univ _) s50 σ hσ _ hfl
    intro h; rw [h] at e; revert e
    generalize ex1.ext0 σ 0 = u; revert u; decide +kernel
  · have e := rel 3 (Finset.mem_univ _) 4 (Finset.mem_univ _) s34 σ hσ _ hfl
    intro h; rw [h] at e; revert e
    generalize ex1.ext0 σ 4 = u; revert u; decide +kernel
  · have e := rel 1 (Finset.mem_univ _) 2 (Finset.mem_univ _) s12 σ hσ _ hfl
    revert e
    generalize ex1.ext0 σ 1 = u; generalize ex1.ext0 σ 2 = v; revert u v; decide +kernel
  · intro u hu
    have hu' : u ∈ ex1.ovPairs := by
      rw [ex1_ovPairs]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
    refine card_rowsWith_cyc (by decide) hu' fun h => ?_
    rw [hadj, cls r2 u hu] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact d12 h.symm
    · exact d23 h
    · exact d24 h
  · rw [hrank, hN, hgam, hcyc]
  · rw [hsol, hgam, hcyc]; norm_num
  · intro σ hσ; rw [hfib σ hσ, hcyc]; norm_num
  · exact P12_card


/-- The heights of a permutation. -/
def ht (p : Equiv.Perm (Fin 6)) : Fin 6 → ℤ := fun i => ((p i : ℕ) : ℤ)

lemma ht_lt (p : Equiv.Perm (Fin 6)) (a b : Fin 6) : ht p a < ht p b ↔ p a < p b := by
  simp only [ht, Nat.cast_lt, ← Fin.lt_def]

lemma ht_injective (p : Equiv.Perm (Fin 6)) : Function.Injective (ht p) := fun a b e =>
  p.injective (Fin.ext (by simpa [ht] using e))

/-- **Example 2, transitive solutions.**  Of the `16` solutions of the rows, `12` are
transitive (induced by a flat-folded state), one for each stacking that satisfies the rows,
and `4` are not. -/
theorem example2_transitive :
    {y | ∃ h, ex1.IsFlat h ∧ ex1.res (xOf h) = y} ⊆ ex1.Sol ∧
    {y | ∃ h, ex1.IsFlat h ∧ ex1.res (xOf h) = y}.ncard = 12 ∧
    (ex1.Sol \ {y | ∃ h, ex1.IsFlat h ∧ ex1.res (xOf h) = y}).ncard = 4 := by
  set T := {y | ∃ h, ex1.IsFlat h ∧ ex1.res (xOf h) = y}
  have hov : ∀ a b : Fin 6, a ≠ b → s(a, b) ∈ ex1.ovPairs := fun a b hab =>
    mk_mem_ovPairs.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hab, (example1).2.1 a b⟩
  have hTS : T ⊆ ex1.Sol := by
    rintro _ ⟨h, hf, rfl⟩; exact res_mem_Sol (antisymm_xOf hf.1) hf.2
  have flat_ht : ∀ p ∈ P12, ex1.IsFlat (ht p) := fun p hp =>
    ⟨fun a _ b _ e => ht_injective p e, (Finset.mem_filter.1 hp).2⟩
  have hT : T = ↑(P12.image fun p => ex1.res (xOf (ht p))) := by
    ext y
    simp only [T, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨h, hf, rfl⟩
      have hinj := injective_of_flat rfl hf
      set p := Equiv.ofBijective (rankOf h) (rankOf_injective hinj).bijective_of_finite
      have hx : xOf h = xOf (ht p) := xOf_rank hinj
      refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by rw [hx]⟩
      have := hf.2
      rw [hx] at this
      exact this
    · rintro ⟨p, hp, rfl⟩
      exact ⟨ht p, flat_ht p hp, rfl⟩
  have hinjOn : Set.InjOn (fun p => ex1.res (xOf (ht p))) ↑P12 := by
    intro p hp q hq e
    apply perm_eq_of_lt_iff
    intro a b
    by_cases hab : a = b
    · subst hab; exact iff_of_false (lt_irrefl _) (lt_irrefl _)
    have e' := congrFun (congrArg lay e) a
    have e'' := congrFun e' b
    rw [lay_res (antisymm_xOf (flat_ht p hp).1) (hov a b hab),
      lay_res (antisymm_xOf (flat_ht q hq).1) (hov a b hab)] at e''
    simp only [xOf, ht_lt] at e''
    by_cases h1 : p a < p b <;> by_cases h2 : q a < q b <;> simp [h1, h2] at e'' ⊢
  have hcard : T.ncard = 12 := by
    rw [hT, Set.ncard_coe_finset, Finset.card_image_of_injOn hinjOn, P12_card]
  refine ⟨hTS, hcard, ?_⟩
  rw [Set.ncard_diff hTS (Set.toFinite _), (example2).2.2.2.2.2.2.2.2.1, hcard]

end Walk

end Origami
