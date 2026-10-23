import Origami.Components
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Theorem 2 by the gauge: the pairing at a vertex without taco–taco rows

Let `e_T` be a highest crease and `e_B` a lowest one.  They cut the sectors into two sides,
`S₁ = f_{B+1}, …, f_T` and `S₂ = f_{T+1}, …, f_B`.  At a vertex without taco–taco rows every
row is a taco–tortilla row `(e_k, f_g)` with `e_k` neither `e_T` nor `e_B`, so its two taco
sectors lie on one side, and its two pairs have the same number of sectors in `S₁`
(`ncls_conn`).  Of the adjacent pairs, only those of `e_T` and `e_B` have one sector on each
side.  Since every component contains an even number of adjacent pairs
(`even_card_sameComp`, valid at every vertex), the component of `e_T` contains exactly the
adjacent pairs of `e_T` and `e_B` (`filter_sameComp_top`).

In the gauge of `e_B` (`Gauge.lean`) every row says that two gauged variables are equal, so
along a component the gauged variable is constant (`symm2_gauge_conn`); this gives the
relation forced on two creases of a component (`asg_add_asg`).

Every component of the row graph contains exactly two adjacent pairs (`card_sameComp`): it
contains an even number of them, and at most two, since a connected graph with `V` vertices
has at least `V - 1` edges while here the rows are the edges and every non-adjacent pair has
degree two.  Each component then has as many rows as pairs minus one; the number of its rows
is even, because every row changes by one the number of maxima among the two sectors of a
pair (`even_card_compRows`), and counting rows through lower ends shows that exactly one of
its two adjacent pairs sits at a maximum (`up_iff_not_up`).  Hence every pair other than
`{e_T, e_B}` joins a maximum to a minimum and is forced opposite, while `e_T` and `e_B` are
forced equal; and `M - V = ±2`, with the sign given by the common assignment of `e_T` and
`e_B` (`pairing`).
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-- The vertex has no taco–taco row: no two creases of the same type on one ray. -/
def NoTC (w : Walk ι α) : Prop := ∀ q l, ¬ w.IsTC q l

lemma generic_noTC (hg : w.Generic) : w.NoTC := fun _ _ ⟨hq, hl, hne, hc, _⟩ => hne (hg hq hl hc)

lemma tcRows_eq_empty_of_noTC (hn : w.NoTC) : w.tcRows = ∅ := by
  ext r
  simp only [Finset.notMem_empty, iff_false]
  intro hr
  obtain ⟨q, l, -, h, -⟩ := mem_tcRows.1 hr
  exact hn q l h

/-! ### Extreme creases and the two sides -/

/-- A crease interior to a sector is not a highest crease. -/
lemma ne_of_isTT_of_max {T q g : ι} (hmax : ∀ k ∈ w.C, w.c k ≤ w.c T) (h : w.IsTT q g) :
    q ≠ T := by
  rintro rfl
  obtain ⟨-, hg, -, h2⟩ := h
  have := hmax _ (uc_mem hg)
  rw [c_uc hg] at this
  exact absurd h2 (not_lt.2 this)

lemma top_ne_bot {T B : ι} (hT : T ∈ w.C) (hmax : ∀ k ∈ w.C, w.c k ≤ w.c T)
    (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) : T ≠ B := by
  rintro rfl
  exact c_prv_ne hT (le_antisymm (hmax _ (w.prv_mem hT)) (hmin _ (w.prv_mem hT)))

/-- The side `S₁`: the sectors met after `B` up to `T` included. -/
def side1 (B T g : ι) : Prop := cbtw B g T ∨ g = T

lemma side1_nxt_iff {B T k : ι} (hB : B ∈ w.C) (hT : T ∈ w.C) (hk : k ∈ w.C) (hkB : k ≠ B)
    (hkT : k ≠ T) : side1 B T k ↔ side1 B T (nxt w.C k) := by
  unfold side1
  rw [or_iff_left hkT]
  exact cbtw_nxt_iff hB hk hT hkB (Ne.symm hkT)

lemma side1_top {B T : ι} : side1 B T T := Or.inr rfl

lemma not_side1_nxt_top {B T : ι} (hB : B ∈ w.C) (hT : T ∈ w.C) (hTB : T ≠ B) :
    ¬ side1 B T (nxt w.C T) := by
  rintro (h | h)
  · exact cbtw_asymm (cbtw_nxt hB hT hTB) h
  · exact w.nxt_ne hT h

lemma not_side1_bot {B T : ι} (hTB : T ≠ B) : ¬ side1 B T B := by
  rintro (h | h)
  · exact not_cbtw_left h
  · exact hTB h.symm

lemma side1_nxt_bot {B T : ι} (hT : T ∈ w.C) :
    side1 B T (nxt w.C B) := by
  by_cases h : nxt w.C B = T
  · exact Or.inr h
  · left
    rcases cbtw_or_cbtw (k := B) h with h1 | h1
    · exact h1
    · exact absurd h1 ((nxt_spec w.nonempty B).2 T hT)

/-- The number of sectors of a pair that lie in `S₁`. -/
noncomputable def ncls (B T : ι) : Sym2 ι → ℕ :=
  Sym2.lift ⟨fun a b => (if side1 B T a then 1 else 0) + (if side1 B T b then 1 else 0),
    fun _ _ => add_comm _ _⟩

@[simp] lemma ncls_mk (B T a b : ι) :
    ncls B T s(a, b) = (if side1 B T a then 1 else 0) + (if side1 B T b then 1 else 0) := rfl

/-- At a vertex without taco–taco rows every row is a taco–tortilla row. -/
lemma eq_tt_of_noTC (hn : w.NoTC) {r : Row ι} (hr : r ∈ w.rows) :
    ∃ q g, w.IsTT q g ∧ r = Row.tt q (nxt w.C q) g := by
  rcases mem_rows.1 hr with h | h
  · exact mem_ttRows.1 h
  · obtain ⟨q, l, -, hql, -⟩ := mem_tcRows.1 h
    exact absurd hql (hn q l)

/-- Rows do not mix the classes `S₁ × S₁`, `S₁ × S₂`, `S₂ × S₂`. -/
lemma ncls_linked (hn : w.NoTC) {B T : ι} (hB : B ∈ w.C) (hT : T ∈ w.C)
    (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) (hmax : ∀ k ∈ w.C, w.c k ≤ w.c T) {u v : Sym2 ι}
    (h : w.Linked u v) : ncls B T u = ncls B T v := by
  obtain ⟨r, hr, hu, hv⟩ := h
  obtain ⟨q, g, hqg, rfl⟩ := eq_tt_of_noTC hn hr
  have e : ncls B T s(q, g) = ncls B T s(nxt w.C q, g) := by
    simp only [ncls_mk]
    rw [show side1 B T q = side1 B T (nxt w.C q) from propext (side1_nxt_iff hB hT hqg.1
      (ne_of_isTT_of_min hmin hqg) (ne_of_isTT_of_max hmax hqg))]
  rw [Row.mem_verts_tt] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact e
  · exact e.symm
  · rfl

lemma ncls_conn (hn : w.NoTC) {B T : ι} (hB : B ∈ w.C) (hT : T ∈ w.C)
    (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) (hmax : ∀ k ∈ w.C, w.c k ≤ w.c T) {u v : Sym2 ι}
    (h : w.Conn u v) : ncls B T u = ncls B T v := by
  induction h with
  | rel a b hab => exact ncls_linked hn hB hT hmin hmax hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Only the adjacent pairs of `e_T` and `e_B` have one sector on each side. -/
lemma ncls_adj_eq_one {B T k : ι} (hB : B ∈ w.C) (hT : T ∈ w.C) (hk : k ∈ w.C) (hTB : T ≠ B) :
    ncls B T (w.adj k) = 1 ↔ k = T ∨ k = B := by
  unfold adj
  rw [ncls_mk]
  by_cases hkT : k = T
  · subst hkT
    simp [side1_top, not_side1_nxt_top hB hk hTB]
  by_cases hkB : k = B
  · subst hkB
    simp [not_side1_bot hTB, side1_nxt_bot hT]
  rw [show side1 B T k = side1 B T (nxt w.C k) from propext (side1_nxt_iff hB hT hk hkB hkT)]
  simp only [hkT, hkB, or_self, iff_false]
  split_ifs <;> omega

/-! ### Every component contains an even number of adjacent pairs -/

/-- **Parity of the components.**  At every walk with at least three creases, every component
of `H_v` contains an even number of adjacent pairs. -/
theorem even_card_sameComp (h3 : 3 ≤ w.C.card) (k₀ : ι) :
    Even (w.C.filter (w.SameComp k₀)).card := by
  have hd : w.SymmOn (fun _ _ => (1 : ZMod 2)) := fun _ _ _ _ _ => rfl
  have := sum_rowsIn_symm (w.Conn (w.adj k₀)) (rowClosed_conn _) hd h3
  have h0 : ∑ r ∈ w.rowsIn (w.Conn (w.adj k₀)), r.eval (fun _ _ => (1 : ZMod 2)) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    cases r <;> simp [Row.eval_tt, Row.eval_tc] <;> decide
  rw [h0, Finset.sum_const, nsmul_eq_mul, mul_one] at this
  exact (ZMod.natCast_eq_zero_iff_even).1 this.symm

/-- The component of `e_T` contains exactly the adjacent pairs of `e_T` and `e_B`. -/
theorem filter_sameComp_top (hn : w.NoTC) (h3 : 3 ≤ w.C.card) {B T : ι} (hB : B ∈ w.C)
    (hT : T ∈ w.C) (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) (hmax : ∀ k ∈ w.C, w.c k ≤ w.c T) :
    w.C.filter (w.SameComp T) = {T, B} := by
  have hTB := top_ne_bot hT hmax hmin
  have hsub : w.C.filter (w.SameComp T) ⊆ {T, B} := by
    intro k hk
    obtain ⟨hk, hc⟩ := Finset.mem_filter.1 hk
    have e := ncls_conn hn hB hT hmin hmax hc
    rw [(ncls_adj_eq_one hB hT hT hTB).2 (Or.inl rfl)] at e
    rcases (ncls_adj_eq_one hB hT hk hTB).1 e.symm with rfl | rfl <;> simp
  have hTm : T ∈ w.C.filter (w.SameComp T) := Finset.mem_filter.2 ⟨hT, conn_refl _⟩
  have hev := even_card_sameComp h3 T
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hTB] at hle
  have hpos := Finset.card_pos.2 ⟨T, hTm⟩
  have h2 : (w.C.filter (w.SameComp T)).card = 2 := by
    obtain ⟨m, hm⟩ := hev; omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [h2, Finset.card_pair hTB])

/-! ### The gauge is constant on components -/

lemma symm2_gauge_linked (hn : w.NoTC) {B : ι} (hB : B ∈ w.C)
    (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) {x : ι → ι → ZMod 2} (hx : w.Antisymm x)
    (hs : w.IsSol x) {u v : Sym2 ι} (h : w.Linked u v) :
    symm2 (x + gauge B) u = symm2 (x + gauge B) v := by
  obtain ⟨r, hr, hu, hv⟩ := h
  obtain ⟨q, g, hqg, rfl⟩ := eq_tt_of_noTC hn hr
  obtain ⟨h1, h2⟩ := tt_distinct hqg
  have hq := hqg.1; have hg := hqg.2.1
  have hy := symmOn_add_gauge hx B
  have e0 := hs _ hr
  rw [Row.eval_tt] at e0
  have eg := gauge_nxt hB hq hg (ne_of_isTT_of_min hmin hqg) (Ne.symm h1) (Ne.symm h2)
  have e : symm2 (x + gauge B) s(q, g) = symm2 (x + gauge B) s(nxt w.C q, g) := by
    rw [symm2_eq hy hq hg h1, symm2_eq hy (w.nxt_mem hq) hg h2]
    simp only [Pi.add_apply]
    rw [eg]
    have : x q g = x (nxt w.C q) g := by
      generalize x q g = a at e0 ⊢; generalize x (nxt w.C q) g = b at e0 ⊢
      revert a b; decide
    rw [this]
  rw [Row.mem_verts_tt] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact e
  · exact e.symm
  · rfl

lemma symm2_gauge_conn (hn : w.NoTC) {B : ι} (hB : B ∈ w.C)
    (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) {x : ι → ι → ZMod 2} (hx : w.Antisymm x)
    (hs : w.IsSol x) {u v : Sym2 ι} (h : w.Conn u v) :
    symm2 (x + gauge B) u = symm2 (x + gauge B) v := by
  induction h with
  | rel a b hab => exact symm2_gauge_linked hn hB hmin hx hs hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The relation forced on a component.**  For two creases whose adjacent pairs lie in one
component, every solution has the same `σ_i + σ_j`, given by the cut and the types. -/
theorem asg_add_asg (hn : w.NoTC) {B : ι} (hB : B ∈ w.C) (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k)
    {x : ι → ι → ZMod 2} (hx : w.Antisymm x) (hs : w.IsSol x) {i j : ι} (hi : i ∈ w.C)
    (hj : j ∈ w.C) (h : w.SameComp i j) :
    w.asg x ⟨i, hi⟩ + w.asg x ⟨j, hj⟩ =
      ((if i = B then 1 else 0) + (if w.up i then 0 else 1)) +
        ((if j = B then 1 else 0) + (if w.up j then 0 else 1)) := by
  have hy := symmOn_add_gauge hx B
  have e := symm2_gauge_conn hn hB hmin hx hs h
  unfold adj at e
  rw [symm2_eq hy hi (w.nxt_mem hi) (w.nxt_ne hi).symm,
    symm2_eq hy hj (w.nxt_mem hj) (w.nxt_ne hj).symm] at e
  simp only [Pi.add_apply] at e
  rw [gauge_adj hB hi, gauge_adj hB hj] at e
  simp only [asg]
  generalize x i (nxt w.C i) = a at e ⊢
  generalize x j (nxt w.C j) = b at e ⊢
  split_ifs at e ⊢ <;> revert a b e <;> decide


/-! ### Counting the rows of a component -/

/-- The pairs of sectors that occur in some row. -/
def allVerts (w : Walk ι α) : Finset (Sym2 ι) := w.rows.biUnion Row.verts

lemma mem_allVerts_of_linked {u v : Sym2 ι} (h : w.Linked u v) : v ∈ w.allVerts := by
  obtain ⟨r, hr, -, hv⟩ := h
  exact Finset.mem_biUnion.2 ⟨r, hr, hv⟩

/-- The pairs of the component of `u₀`. -/
noncomputable def compVerts (w : Walk ι α) (u₀ : Sym2 ι) : Finset (Sym2 ι) :=
  w.allVerts.filter (w.Conn u₀)

/-- At a vertex without taco–taco rows every row has two vertices. -/
lemma card_verts_of_noTC (hn : w.NoTC) {r : Row ι} (hr : r ∈ w.rows) : r.verts.card = 2 := by
  obtain ⟨q, g, hqg, rfl⟩ := eq_tt_of_noTC hn hr
  obtain ⟨h1, -⟩ := tt_distinct hqg
  have hq := hqg.1
  have hne : s(q, g) ≠ s(nxt w.C q, g) := by
    rw [Ne, Sym2.eq_iff]; push_neg
    exact ⟨fun e => absurd e.symm (w.nxt_ne hq), fun e => absurd e h1⟩
  simp only [Row.verts, Row.terms, List.map_cons, List.map_nil, List.toFinset_cons,
    List.toFinset_nil, insert_empty_eq]
  exact Finset.card_pair hne

/-- **Double counting in a component**, with the rows weighted by a predicate. -/
lemma sum_card_rowsWith_filter (u₀ : Sym2 ι) (L : Row ι → Prop) [DecidablePred L] :
    ∑ u ∈ w.compVerts u₀, ((w.rowsWith u).filter L).card =
      ∑ r ∈ (w.rowsIn (w.Conn u₀)).filter L, r.verts.card := by
  have h1 : ∀ u ∈ w.compVerts u₀, ((w.rowsWith u).filter L).card =
      ∑ r ∈ w.rows, if u ∈ r.verts ∧ L r then 1 else 0 := by
    intro u _
    rw [rowsWith, Finset.filter_filter, Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ r ∈ w.rows, (∑ u ∈ w.compVerts u₀, if u ∈ r.verts ∧ L r then 1 else 0) =
      if r ∈ (w.rowsIn (w.Conn u₀)).filter L then r.verts.card else 0 := by
    intro r hr
    rw [← Finset.card_filter]
    by_cases hL : L r
    · simp only [hL, and_true]
      by_cases hin : r ∈ w.rowsIn (w.Conn u₀)
      · rw [if_pos (Finset.mem_filter.2 ⟨hin, hL⟩)]
        congr 1
        ext v
        simp only [Finset.mem_filter, compVerts]
        constructor
        · exact fun h => h.2
        · intro hv
          obtain ⟨-, u, hu, hc⟩ := Finset.mem_filter.1 hin
          exact ⟨⟨Finset.mem_biUnion.2 ⟨r, hr, hv⟩, rowClosed_conn u₀ r hr u hu v hv hc⟩, hv⟩
      · rw [if_neg (fun h => hin (Finset.mem_filter.1 h).1), Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]
        intro v hv hvr
        exact hin (Finset.mem_filter.2 ⟨hr, v, hvr, (Finset.mem_filter.1 hv).2⟩)
    · simp only [hL, and_false, Finset.filter_false, Finset.card_empty]
      rw [if_neg (fun h => hL (Finset.mem_filter.1 h).2)]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, rowsIn]
  tauto

/-- The number of rows through a pair that occurs in a row. -/
lemma card_rowsWith_of_mem (h3 : 3 ≤ w.C.card) {u : Sym2 ι} (hu : u ∈ w.allVerts) :
    (w.rowsWith u).card = if u ∈ w.adjPairs then 1 else 2 := by
  induction u using Sym2.ind with
  | _ a b =>
  obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.1 hu
  have hab : a ≠ b := fun e => diag_not_mem_verts hr a (e ▸ hm)
  have hs := verts_subset_sym2 hr hm
  rw [Finset.mk_mem_sym2_iff] at hs
  rw [card_rowsWith hs.1 hs.2 hab h3, if_pos (overlap_of_mem_verts hr hm)]
  by_cases h : w.Adj a b
  · rw [if_pos h, if_pos ((mem_adjPairs_iff hs.1 hs.2).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((mem_adjPairs_iff hs.1 hs.2).1 h'))]

/-- Adjacent pairs occur in a row. -/
lemma adj_mem_allVerts (h3 : 3 ≤ w.C.card) {k : ι} (hk : k ∈ w.C) : w.adj k ∈ w.allVerts := by
  have := card_rowsWith (w := w) hk (w.nxt_mem hk) (w.nxt_ne hk).symm h3
  rw [if_pos (overlap_nxt hk), if_pos (show w.Adj k (nxt w.C k) from Or.inl rfl)] at this
  obtain ⟨r, hr⟩ := Finset.card_pos.1 (by omega : 0 < (w.rowsWith s(k, nxt w.C k)).card)
  obtain ⟨hr, hm⟩ := Finset.mem_filter.1 hr
  exact Finset.mem_biUnion.2 ⟨r, hr, hm⟩

/-- The adjacent pairs of a component, counted by their creases. -/
lemma card_filter_compVerts (h3 : 3 ≤ w.C.card) (k₀ : ι) (P : ι → Prop) [DecidablePred P] :
    ((w.compVerts (w.adj k₀)).filter (· ∈ (w.C.filter P).image w.adj)).card =
      ((w.C.filter (w.SameComp k₀)).filter P).card := by
  have hinj : Set.InjOn w.adj ↑((w.C.filter (w.SameComp k₀)).filter P) := fun a ha b hb h =>
    mk_nxt_injOn h3 (Finset.mem_of_mem_filter a (Finset.mem_of_mem_filter a ha))
      (Finset.mem_of_mem_filter b (Finset.mem_of_mem_filter b hb)) h
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_image, compVerts]
  constructor
  · rintro ⟨⟨-, hc⟩, k, ⟨hk, hP⟩, rfl⟩
    exact ⟨k, ⟨⟨hk, hc⟩, hP⟩, rfl⟩
  · rintro ⟨k, ⟨⟨hk, hc⟩, hP⟩, rfl⟩
    exact ⟨⟨adj_mem_allVerts h3 hk, hc⟩, k, ⟨hk, hP⟩, rfl⟩

/-- The sum of the numbers of vertices of rows without taco–taco rows. -/
lemma sum_card_verts (hn : w.NoTC) {s : Finset (Row ι)} (hs : s ⊆ w.rows) :
    ∑ r ∈ s, r.verts.card = 2 * s.card := by
  rw [Finset.sum_congr rfl fun r hr => card_verts_of_noTC hn (hs hr), Finset.sum_const,
    smul_eq_mul, mul_comm]

/-- The degrees in a component: `∑ deg + (number of adjacent pairs) = 2 · (number of pairs)`. -/
lemma sum_card_rowsWith_add (h3 : 3 ≤ w.C.card) (k₀ : ι) :
    ∑ u ∈ w.compVerts (w.adj k₀), (w.rowsWith u).card + (w.C.filter (w.SameComp k₀)).card =
      2 * (w.compVerts (w.adj k₀)).card := by
  have e := card_filter_compVerts h3 k₀ (fun _ => True)
  simp only [Finset.filter_true] at e
  have e' : ((w.compVerts (w.adj k₀)).filter (· ∈ w.adjPairs)).card =
      (w.C.filter (w.SameComp k₀)).card := e
  rw [← e', Finset.card_filter, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun u hu => by
    rw [card_rowsWith_of_mem h3 (Finset.mem_of_mem_filter u hu)]]
  rw [Finset.sum_congr rfl fun u _ => show ((if u ∈ w.adjPairs then 1 else 2) +
    (if u ∈ w.adjPairs then 1 else 0) : ℕ) = 2 by split_ifs <;> rfl]
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### The graph of the rows -/

/-- Two distinct pairs are adjacent in the row graph if some row contains both. -/
def rowGraph (w : Walk ι α) : SimpleGraph (Sym2 ι) where
  Adj u v := u ≠ v ∧ w.Linked u v
  symm u v h := ⟨h.1.symm, by obtain ⟨r, hr, hu, hv⟩ := h.2; exact ⟨r, hr, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma reachable_of_conn {u v : Sym2 ι} (h : w.Conn u v) : w.rowGraph.Reachable u v := by
  induction h with
  | rel a b hab =>
    by_cases e : a = b
    · subst e; rfl
    · exact SimpleGraph.Adj.reachable ⟨e, hab⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

lemma conn_of_reachable {u v : Sym2 ι} (h : w.rowGraph.Reachable u v) :
    w.Conn u v ∧ (v = u ∨ v ∈ w.allVerts) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨conn_refl _, Or.inl rfl⟩
  | tail _ hab ih =>
    exact ⟨conn_trans ih.1 (conn_of_linked hab.2), Or.inr (mem_allVerts_of_linked hab.2)⟩

/-- A component has at most one pair more than rows: a connected graph with `V` vertices has
at least `V - 1` edges, and distinct edges come from distinct rows. -/
lemma card_compVerts_le (hn : w.NoTC) {u₀ : Sym2 ι} (hu₀ : u₀ ∈ w.allVerts) :
    (w.compVerts u₀).card ≤ (w.rowsIn (w.Conn u₀)).card + 1 := by
  set G := w.rowGraph
  set c := G.connectedComponentMk u₀
  have hsupp : c.supp = ↑(w.compVerts u₀) := by
    ext v
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
      Finset.mem_coe, compVerts, Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨hc, hv⟩ := conn_of_reachable h.symm
      refine ⟨?_, hc⟩
      rcases hv with rfl | hv
      · exact hu₀
      · exact hv
    · rintro ⟨-, hc⟩
      exact (reachable_of_conn hc).symm
  have hV : Nat.card c = (w.compVerts u₀).card := by
    have : Nat.card c = Nat.card c.supp := rfl
    rw [this, hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  -- every edge comes from a row of the component
  have hedge : ∀ e ∈ c.toSimpleGraph.edgeSet,
      ∃ r ∈ w.rowsIn (w.Conn u₀), ∀ x ∈ e, x.1 ∈ r.verts := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    obtain ⟨-, r, hr, ha, hb⟩ := he
    have ha : a.1 ∈ r.verts := ha
    have hb : b.1 ∈ r.verts := hb
    have hca : w.Conn u₀ a.1 := by
      have : a.1 ∈ c.supp := a.2
      rw [hsupp, Finset.mem_coe, compVerts, Finset.mem_filter] at this
      exact this.2
    refine ⟨r, Finset.mem_filter.2 ⟨hr, a.1, ha, hca⟩, fun x hx => ?_⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact ha
    · exact hb
  let f : c.toSimpleGraph.edgeSet → w.rowsIn (w.Conn u₀) := fun e =>
    ⟨Classical.choose (hedge e.1 e.2), (Classical.choose_spec (hedge e.1 e.2)).1⟩
  -- distinct edges come from distinct rows, since a row has two vertices
  have hf : Function.Injective f := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ h
    have h1 := (Classical.choose_spec (hedge e he)).2
    have h2 := (Classical.choose_spec (hedge e' he')).2
    simp only [f, Subtype.mk.injEq] at h
    rw [h] at h1
    set r := Classical.choose (hedge e' he')
    have hr : r ∈ w.rows := Finset.mem_of_mem_filter _ (Classical.choose_spec (hedge e' he')).1
    have hcard := card_verts_of_noTC hn hr
    have key : ∀ z ∈ c.toSimpleGraph.edgeSet, (∀ x ∈ z, x.1 ∈ r.verts) →
        ∀ x : c.supp, x ∈ z ↔ x.1 ∈ r.verts := by
      intro z hz hzr x
      induction z using Sym2.ind with
      | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at hz
      have hab : a.1 ≠ b.1 := hz.1
      have ha := hzr a (Sym2.mem_mk_left a b)
      have hb := hzr b (Sym2.mem_mk_right a b)
      obtain ⟨p, q, hpq, hrv⟩ := Finset.card_eq_two.1 hcard
      have hset : r.verts = {a.1, b.1} := by
        rw [hrv] at ha hb ⊢
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact absurd (ha.trans hb.symm) hab
        · rw [ha, hb]
        · rw [ha, hb, Finset.pair_comm]
        · exact absurd (ha.trans hb.symm) hab
      rw [hset, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff,
        Subtype.ext_iff]
    exact Subtype.ext (Sym2.ext fun x => (key e he h1 x).trans (key e' he' h2 x).symm)
  have hE : Nat.card c.toSimpleGraph.edgeSet ≤ (w.rowsIn (w.Conn u₀)).card := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_finsetCard] at this
  have := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  rw [← hV]
  omega

/-- **Every component contains exactly two adjacent pairs**, at a vertex without taco–taco
rows, and it has one pair more than rows. -/
theorem card_sameComp (hn : w.NoTC) (h3 : 3 ≤ w.C.card) {k₀ : ι} (hk₀ : k₀ ∈ w.C) :
    (w.C.filter (w.SameComp k₀)).card = 2 ∧
      (w.rowsIn (w.Conn (w.adj k₀))).card + 1 = (w.compVerts (w.adj k₀)).card := by
  have hdeg := sum_card_rowsWith_filter (w := w) (w.adj k₀) (fun _ => True)
  simp only [Finset.filter_true] at hdeg
  rw [sum_card_verts hn (s := w.rowsIn (w.Conn (w.adj k₀))) (Finset.filter_subset _ _)] at hdeg
  have hsum := sum_card_rowsWith_add h3 k₀
  have hle := card_compVerts_le hn (adj_mem_allVerts h3 hk₀)
  have hev := even_card_sameComp h3 k₀
  have hpos : 0 < (w.C.filter (w.SameComp k₀)).card :=
    Finset.card_pos.2 ⟨k₀, Finset.mem_filter.2 ⟨hk₀, conn_refl _⟩⟩
  obtain ⟨m, hm⟩ := hev
  constructor <;> omega


/-! ### Each pair joins a maximum to a minimum -/

/-- A row through lower ends of intervals: at a minimum crease. -/
def IsLowRow (w : Walk ι α) : Row ι → Prop
  | .tt q _ _ => ¬ w.up q
  | .tc q _ _ _ => ¬ w.up q

lemma filter_low_rowsWith {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hov : w.Overlap a b) :
    (w.rowsWith s(a, b)).filter w.IsLowRow = w.lowRows a b := by
  rw [rowsWith_eq ha hb hov, Finset.filter_union]
  have h1 : (w.lowRows a b).filter w.IsLowRow = w.lowRows a b := by
    rw [Finset.filter_true_of_mem]
    intro r hr
    unfold lowRows at hr
    split_ifs at hr <;> simp only [Finset.mem_singleton, Finset.notMem_empty] at hr <;>
      subst hr <;> simp [IsLowRow, not_up_lc ha, not_up_lc hb]
  have h2 : (w.upRows a b).filter w.IsLowRow = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro r hr
    unfold upRows at hr
    split_ifs at hr <;> simp only [Finset.mem_singleton, Finset.notMem_empty] at hr <;>
      subst hr <;> simp [IsLowRow, up_uc ha, up_uc hb]
  rw [h1, h2, Finset.union_empty]

lemma lc_nxt_iff (h3 : 3 ≤ w.C.card) {k : ι} (hk : k ∈ w.C) :
    w.lc k = w.lc (nxt w.C k) ↔ ¬ w.up k := by
  unfold lc
  by_cases hu : w.up k
  · have hn : ¬ w.up (nxt w.C k) := fun h => (up_nxt hk).1 h hu
    rw [if_pos hu, if_neg hn]
    simp only [hu, not_true_eq_false, iff_false]
    exact (nxt_ne_prv hk h3).symm
  · have hn : w.up (nxt w.C k) := (up_nxt hk).2 hu
    rw [if_neg hu, if_pos hn, prv_nxt hk]
    simp [hu]

/-- The number of rows through the lower ends of a pair: one, except for the adjacent pair of
a minimum, whose two sectors share their lower crease. -/
lemma card_low_add (h3 : 3 ≤ w.C.card) {u : Sym2 ι} (hu : u ∈ w.allVerts) :
    ((w.rowsWith u).filter w.IsLowRow).card +
      (if u ∈ (w.C.filter fun k => ¬ w.up k).image w.adj then 1 else 0) = 1 := by
  induction u using Sym2.ind with
  | _ a b =>
  obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.1 hu
  have hab : a ≠ b := fun e => diag_not_mem_verts hr a (e ▸ hm)
  have hs := verts_subset_sym2 hr hm
  rw [Finset.mk_mem_sym2_iff] at hs
  rw [filter_low_rowsWith hs.1 hs.2 (overlap_of_mem_verts hr hm), card_lowRows hs.1 hs.2]
  have hiff : w.lc a = w.lc b ↔ s(a, b) ∈ (w.C.filter fun k => ¬ w.up k).image w.adj := by
    rw [Finset.mem_image]
    constructor
    · intro h
      rcases (share_iff_adj hs.1 hs.2 hab).1 (Or.inl h) with rfl | rfl
      · exact ⟨a, Finset.mem_filter.2 ⟨hs.1, (lc_nxt_iff h3 hs.1).1 h⟩, rfl⟩
      · exact ⟨b, Finset.mem_filter.2 ⟨hs.2, (lc_nxt_iff h3 hs.2).1 h.symm⟩, Sym2.eq_swap⟩
    · rintro ⟨k, hk, he⟩
      obtain ⟨hk, hku⟩ := Finset.mem_filter.1 hk
      unfold adj at he
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (lc_nxt_iff h3 hk).2 hku
      · exact ((lc_nxt_iff h3 hk).2 hku).symm
  by_cases h : w.lc a = w.lc b
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

/-- **Each pair joins a maximum to a minimum.**  If two distinct creases lie in one
component, exactly one of them is a maximum.  The component has one pair more than rows, an
even number of rows (each row changes by one the number of maxima among the end creases of
the two sectors of a pair), and every pair has one row through its lower ends, except the
adjacent pair of a minimum. -/
theorem up_iff_not_up (hn : w.NoTC) (h3 : 3 ≤ w.C.card) {i j : ι} (hi : i ∈ w.C) (hj : j ∈ w.C)
    (hij : i ≠ j) (h : w.SameComp i j) : w.up i ↔ ¬ w.up j := by
  obtain ⟨hA, hRK⟩ := card_sameComp hn h3 hi
  have hfil : w.C.filter (w.SameComp i) = {i, j} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hi, conn_refl _⟩
      · exact Finset.mem_filter.2 ⟨hj, h⟩
    · rw [hA, Finset.card_pair hij]
  -- the number of rows of the component is even
  set d : ι → ι → ZMod 2 := fun a b => (if w.up a then 1 else 0) + (if w.up b then 1 else 0)
    with hd_def
  have hd : w.SymmOn d := fun _ _ _ _ _ => add_comm _ _
  have hpar := sum_rowsIn_symm (w.Conn (w.adj i)) (rowClosed_conn _) hd h3
  have hrow : ∀ r ∈ w.rowsIn (w.Conn (w.adj i)), r.eval d = 1 := by
    intro r hr
    obtain ⟨q, g, hqg, rfl⟩ := eq_tt_of_noTC hn (Finset.mem_of_mem_filter r hr)
    rw [Row.eval_tt]
    have hun := up_nxt hqg.1
    by_cases hq : w.up q
    · have : ¬ w.up (nxt w.C q) := fun h' => hun.1 h' hq
      simp only [hd_def, hq, this, if_true, if_false]
      split_ifs <;> decide
    · have : w.up (nxt w.C q) := hun.2 hq
      simp only [hd_def, hq, this, if_true, if_false]
      split_ifs <;> decide
  have hadj1 : ∀ k ∈ w.C.filter (fun k => w.Conn (w.adj i) (w.adj k)), d k (nxt w.C k) = 1 := by
    intro k hk
    have hun := up_nxt (Finset.mem_of_mem_filter k hk)
    by_cases hq : w.up k
    · have : ¬ w.up (nxt w.C k) := fun h' => hun.1 h' hq
      simp [hd_def, hq, this]
    · have : w.up (nxt w.C k) := hun.2 hq
      simp [hd_def, hq, this]
  rw [Finset.sum_congr rfl hrow, Finset.sum_congr rfl hadj1, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one] at hpar
  have hA' : (w.C.filter (fun k => w.Conn (w.adj i) (w.adj k))).card = 2 := hA
  rw [hA'] at hpar
  have hReven : Even (w.rowsIn (w.Conn (w.adj i))).card :=
    (ZMod.natCast_eq_zero_iff_even).1 (by rw [hpar]; rfl)
  -- the rows through lower ends
  have hlow := sum_card_rowsWith_filter (w := w) (w.adj i) w.IsLowRow
  rw [sum_card_verts hn (s := (w.rowsIn (w.Conn (w.adj i))).filter w.IsLowRow)
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))] at hlow
  have hlow2 : ∑ u ∈ w.compVerts (w.adj i), ((w.rowsWith u).filter w.IsLowRow).card +
      ((w.compVerts (w.adj i)).filter
        (· ∈ (w.C.filter fun k => ¬ w.up k).image w.adj)).card =
      (w.compVerts (w.adj i)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib,
      Finset.sum_congr (s₁ := w.compVerts (w.adj i)) rfl fun u hu =>
        card_low_add h3 (Finset.mem_filter.1 hu).1,
      Finset.sum_const, smul_eq_mul, mul_one]
  rw [card_filter_compVerts h3 i (fun k => ¬ w.up k), hfil] at hlow2
  obtain ⟨t, ht⟩ := hReven
  by_cases hui : w.up i <;> by_cases huj : w.up j
  · exfalso
    rw [Finset.filter_eq_empty_iff.2 (by
      intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simpa)] at hlow2
    simp only [Finset.card_empty, add_zero] at hlow2
    omega
  · simp [hui, huj]
  · simp [hui, huj]
  · exfalso
    rw [Finset.filter_true_of_mem (by
      intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption), Finset.card_pair hij] at hlow2
    omega

/-! ### Theorem 2 -/

lemma up_of_max {T : ι} (hT : T ∈ w.C) (hmax : ∀ k ∈ w.C, w.c k ≤ w.c T) : w.up T :=
  lt_of_le_of_ne (hmax _ (w.prv_mem hT)) (c_prv_ne hT)

lemma not_up_of_min {B : ι} (hB : B ∈ w.C) (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) : ¬ w.up B := by
  rw [not_up_iff hB]
  exact lt_of_le_of_ne (hmin _ (w.prv_mem hB)) (c_prv_ne hB).symm

/-- Two creases paired with a third one coincide. -/
lemma eq_of_sameComp (hn : w.NoTC) (h3 : 3 ≤ w.C.card) {i j j' : ι} (hi : i ∈ w.C)
    (hj : j ∈ w.C) (hj' : j' ∈ w.C) (hji : j ≠ i) (hj'i : j' ≠ i) (h : w.SameComp i j)
    (h' : w.SameComp i j') : j = j' := by
  by_contra hne
  have hsub : ({i, j, j'} : Finset ι) ⊆ w.C.filter (w.SameComp i) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.2 ⟨hi, conn_refl _⟩
    · exact Finset.mem_filter.2 ⟨hj, h⟩
    · exact Finset.mem_filter.2 ⟨hj', h'⟩
  have hc := Finset.card_le_card hsub
  rw [(card_sameComp hn h3 hi).1, Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hji, Ne.symm hj'i⟩), Finset.card_pair hne] at hc
  omega

/-- **Theorem 2 (the pairing at a vertex without taco–taco rows).**  Let `e_T` be a highest
crease and `e_B` a lowest one.  Every component of `H_v` containing an adjacent pair contains
exactly two, so the rows pair the creases; the component of `e_T` pairs it with `e_B`; every
pair joins a maximum to a minimum.  In every solution of the rows, transitive or not, `e_T`
and `e_B` receive equal assignments, every other pair opposite ones, and
`M - V = 2 σ(e_T)`, that is `2` or `-2` according as `e_T` is a mountain or a valley. -/
theorem pairing (hn : w.NoTC) (h3 : 3 ≤ w.C.card) {B T : ι} (hB : B ∈ w.C) (hT : T ∈ w.C)
    (hmin : ∀ k ∈ w.C, w.c B ≤ w.c k) (hmax : ∀ k ∈ w.C, w.c k ≤ w.c T) :
    (∀ i ∈ w.C, (w.C.filter (w.SameComp i)).card = 2) ∧
    w.C.filter (w.SameComp T) = {T, B} ∧
    (∀ i ∈ w.C, ∀ j ∈ w.C, i ≠ j → w.SameComp i j → (w.up i ↔ ¬ w.up j)) ∧
    ∀ x : ι → ι → ZMod 2, w.Antisymm x → w.IsSol x →
      w.asg x ⟨T, hT⟩ = w.asg x ⟨B, hB⟩ ∧
      (∀ i (hi : i ∈ w.C) j (hj : j ∈ w.C), i ≠ j → w.SameComp i j → ¬ w.SameComp i T →
        w.asg x ⟨i, hi⟩ ≠ w.asg x ⟨j, hj⟩) ∧
      w.mv (w.asg x) = if w.asg x ⟨T, hT⟩ = 0 then 2 else -2 := by
  have hTB := top_ne_bot hT hmax hmin
  have htop := filter_sameComp_top hn h3 hB hT hmin hmax
  have hTBc : w.SameComp T B := by
    have : B ∈ w.C.filter (w.SameComp T) := by rw [htop]; simp
    exact (Finset.mem_filter.1 this).2
  -- a crease not paired with `e_T` is neither `e_T` nor `e_B`
  have hout : ∀ i ∈ w.C, ¬ w.SameComp i T → i ≠ T ∧ i ≠ B := by
    intro i _ h
    refine ⟨fun e => h (e ▸ conn_refl _), fun e => h ?_⟩
    rw [e]; exact conn_symm hTBc
  -- the relation forced on two creases of a component, outside the component of `e_T`
  have hopp : ∀ x : ι → ι → ZMod 2, w.Antisymm x → w.IsSol x →
      ∀ i (hi : i ∈ w.C) j (hj : j ∈ w.C), i ≠ j → w.SameComp i j → ¬ w.SameComp i T →
        w.asg x ⟨i, hi⟩ ≠ w.asg x ⟨j, hj⟩ := by
    intro x hx hs i hi j hj hij h hT'
    have hjT : ¬ w.SameComp j T := fun h' => hT' (conn_trans h h')
    obtain ⟨-, hiB⟩ := hout i hi hT'
    obtain ⟨-, hjB⟩ := hout j hj hjT
    have e := asg_add_asg hn hB hmin hx hs hi hj h
    have hud := up_iff_not_up hn h3 hi hj hij h
    rw [if_neg hiB, if_neg hjB] at e
    intro heq
    rw [heq] at e
    by_cases hu : w.up i
    · have : ¬ w.up j := hud.1 hu
      simp only [hu, this, if_true, if_false] at e
      revert e; generalize w.asg x ⟨j, hj⟩ = a; revert a; decide
    · have : w.up j := by by_contra h'; exact hu (hud.2 h')
      simp only [hu, this, if_true, if_false] at e
      revert e; generalize w.asg x ⟨j, hj⟩ = a; revert a; decide
  refine ⟨fun i hi => (card_sameComp hn h3 hi).1, htop,
    fun i hi j hj hij h => up_iff_not_up hn h3 hi hj hij h, fun x hx hs => ?_⟩
  have hTBeq : w.asg x ⟨T, hT⟩ = w.asg x ⟨B, hB⟩ := by
    have e := asg_add_asg hn hB hmin hx hs hT hB hTBc
    rw [if_neg hTB, if_pos rfl, if_pos (up_of_max hT hmax), if_neg (not_up_of_min hB hmin)] at e
    revert e
    generalize w.asg x ⟨T, hT⟩ = a; generalize w.asg x ⟨B, hB⟩ = b
    revert a b; decide
  refine ⟨hTBeq, hopp x hx hs, ?_⟩
  -- `M - V`: the other creases cancel in pairs
  have hpart : ∀ i ∈ w.C, ∃ j ∈ w.C, j ≠ i ∧ w.SameComp i j := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne
      (by rw [(card_sameComp hn h3 hi).1]; norm_num) i
    exact ⟨j, Finset.mem_of_mem_filter j hj, hji, (Finset.mem_filter.1 hj).2⟩
  choose! p hpC hpne hps using hpart
  set E : ι → ℤ := fun k => if (x k (nxt w.C k) + if w.up k then 0 else 1) = 1 then -1 else 1
    with hE
  have hmv : w.mv (w.asg x) = ∑ k ∈ w.C, E k := by
    rw [← Finset.sum_coe_sort w.C E]
    have : ∀ k : w.C, E k.1 = 1 - 2 * (if w.asg x k = 1 then 1 else 0) := by
      intro k; simp only [hE, asg]; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_sub_distrib, ← Finset.mul_sum]
    unfold mv nV
    rw [Finset.card_filter]
    push_cast
    simp
  set S := (w.C.erase T).erase B
  have hS : ∀ i ∈ S, i ∈ w.C ∧ ¬ w.SameComp i T := by
    intro i hi
    obtain ⟨hiB, hi'⟩ := Finset.mem_erase.1 hi
    obtain ⟨hiT, hiC⟩ := Finset.mem_erase.1 hi'
    refine ⟨hiC, fun h => ?_⟩
    have : i ∈ w.C.filter (w.SameComp T) := Finset.mem_filter.2 ⟨hiC, conn_symm h⟩
    rw [htop] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  have hpS : ∀ i ∈ S, p i ∈ S := by
    intro i hi
    obtain ⟨hiC, hiT⟩ := hS i hi
    have hpT : ¬ w.SameComp (p i) T := fun h => hiT (conn_trans (hps i hiC) h)
    obtain ⟨h1, h2⟩ := hout (p i) (hpC i hiC) hpT
    exact Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hpC i hiC⟩⟩
  have hS0 : ∑ k ∈ S, E k = 0 := by
    refine Finset.sum_involution (fun a _ => p a) (fun a ha => ?_) (fun a ha _ => hpne a (hS a ha).1)
      (fun a ha => hpS a ha) (fun a ha => ?_)
    · obtain ⟨haC, haT⟩ := hS a ha
      have hne := hopp x hx hs a haC (p a) (hpC a haC) (hpne a haC).symm (hps a haC) haT
      simp only [asg] at hne
      simp only [hE]
      revert hne
      generalize x a (nxt w.C a) + (if w.up a then 0 else 1) = u
      generalize x (p a) (nxt w.C (p a)) + (if w.up (p a) then 0 else 1) = v
      revert u v; decide
    · obtain ⟨haC, -⟩ := hS a ha
      have hpa := hpC a haC
      exact (eq_of_sameComp hn h3 hpa (hpC _ hpa) haC (hpne _ hpa) (hpne a haC).symm
        (hps _ hpa) (conn_symm (hps a haC)))
  have hBT : B ∈ w.C.erase T := Finset.mem_erase.2 ⟨Ne.symm hTB, hB⟩
  rw [hmv, ← Finset.add_sum_erase _ _ hT, ← Finset.add_sum_erase _ _ hBT, hS0, add_zero]
  have hEB : E B = E T := by
    have : w.asg x ⟨B, hB⟩ = w.asg x ⟨T, hT⟩ := hTBeq.symm
    simp only [asg] at this
    simp only [hE, this]
  rw [hEB]
  have key : ∀ u : ZMod 2,
      ((if u = 1 then -1 else 1) + (if u = 1 then -1 else 1) : ℤ) = if u = 0 then 2 else -2 := by
    decide
  exact key _

end Walk

end Origami
