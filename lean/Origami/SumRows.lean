import Origami.TwoRows
import Mathlib.Data.Sym.Sym2.Finsupp
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The linear part of Theorem 1

Summing all the rows at a vertex, every adjacent pair of sectors occurs once and every
other overlapping pair twice (Lemma 2).  Hence, for any `d` that is symmetric on the
sectors, the sum of the rows evaluated at `d` equals `∑_k d k (nxt k)`.  Applied to the
difference of two assignments of the layer variables, this says that

  `∑_{rows} r.eval x + ∑_k x k (nxt k)`

does not depend on the antisymmetric `x`: it is a constant, which `Theorem1.lean` computes.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Reading a function of two sectors on unordered pairs, through the increasing order. -/
def symm2 (d : ι → ι → ZMod 2) : Sym2 ι → ZMod 2 :=
  Sym2.lift ⟨fun i j => d (min i j) (max i j), fun i j => by simp only [min_comm, max_comm]⟩

@[simp] lemma symm2_mk (d : ι → ι → ZMod 2) (i j : ι) :
    symm2 d s(i, j) = d (min i j) (max i j) := rfl

namespace Walk

variable {w : Walk ι α}

/-- `d` is symmetric on pairs of distinct sectors. -/
def SymmOn (w : Walk ι α) (d : ι → ι → ZMod 2) : Prop :=
  ∀ i ∈ w.C, ∀ j ∈ w.C, i ≠ j → d j i = d i j

lemma symm2_eq {d : ι → ι → ZMod 2} (hd : w.SymmOn d) {i j : ι} (hi : i ∈ w.C) (hj : j ∈ w.C)
    (hij : i ≠ j) : symm2 d s(i, j) = d i j := by
  rw [symm2_mk]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
  · rw [min_eq_right h.le, max_eq_left h.le, hd i hi j hj hij]

/-- The ends of a sector are not interior to it. -/
lemma not_mem_interior_end {g : ι} :
    ¬ (w.lo g < w.c g ∧ w.c g < w.hi g) ∧ ¬ (w.lo g < w.c (prv w.C g) ∧ w.c (prv w.C g) < w.hi g) := by
  unfold lo hi
  constructor <;> rintro ⟨h1, h2⟩
  · rcases le_total (w.c (prv w.C g)) (w.c g) with h | h
    · rw [max_eq_right h] at h2; exact lt_irrefl _ h2
    · rw [min_eq_right h] at h1; exact lt_irrefl _ h1
  · rcases le_total (w.c (prv w.C g)) (w.c g) with h | h
    · rw [min_eq_left h] at h1; exact lt_irrefl _ h1
    · rw [max_eq_left h] at h2; exact lt_irrefl _ h2

/-- The sectors of a taco–tortilla row are distinct. -/
lemma tt_distinct {q g : ι} (h : w.IsTT q g) : q ≠ g ∧ nxt w.C q ≠ g := by
  obtain ⟨hq, hg, h1, h2⟩ := h
  have := not_mem_interior_end (w := w) (g := g)
  refine ⟨fun e => ?_, fun e => ?_⟩
  · subst e; exact this.1 ⟨h1, h2⟩
  · subst e; rw [prv_nxt hq] at this; exact this.2 ⟨h1, h2⟩

/-- The four sectors of a taco–taco row are distinct. -/
lemma tc_distinct {q l : ι} (h : w.IsTC q l) :
    q ≠ l ∧ q ≠ nxt w.C l ∧ nxt w.C q ≠ l ∧ nxt w.C q ≠ nxt w.C l := by
  obtain ⟨hq, hl, hne, heq, -⟩ := h
  refine ⟨hne, fun e => ?_, fun e => ?_, fun e => hne (nxt_injOn hq hl e)⟩
  · exact c_nxt_ne hl (by rw [← e]; exact heq)
  · exact c_nxt_ne hq (by rw [e]; exact heq.symm)

/-- A row, evaluated at a symmetric `d`, is the sum of `d` over its vertices. -/
lemma eval_eq_sum_verts {d : ι → ι → ZMod 2} (hd : w.SymmOn d) {r : Row ι} (hr : r ∈ w.rows) :
    r.eval d = ∑ u ∈ r.verts, symm2 d u := by
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, hqg, rfl⟩ := mem_ttRows.1 hr
    obtain ⟨h1, h2⟩ := tt_distinct hqg
    have hq := hqg.1; have hg := hqg.2.1
    have hne : s(q, g) ≠ s(nxt w.C q, g) := by
      rw [Ne, Sym2.eq_iff]; push_neg
      exact ⟨fun e => absurd e.symm (w.nxt_ne hq), fun e => absurd e h1⟩
    simp only [Row.verts, Row.terms, Row.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
    rw [Finset.sum_pair hne, symm2_eq hd hq hg h1, symm2_eq hd (w.nxt_mem hq) hg h2]
  · obtain ⟨q, l, -, hql, rfl⟩ := mem_tcRows.1 hr
    obtain ⟨d1, d2, d3, d4⟩ := tc_distinct hql
    have hq := hql.1; have hl := hql.2.1
    have hnq := w.nxt_mem hq; have hnl := w.nxt_mem hl
    have e1 := w.nxt_ne hq; have e2 := w.nxt_ne hl
    simp only [Row.verts, Row.terms, Row.eval, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [List.sum_toFinset _ (by
      simp [List.nodup_cons, d1, d2, d4, e1, Ne.symm d1, Ne.symm d3, Ne.symm d4, Ne.symm e1,
        Ne.symm e2])]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [symm2_eq hd hq hl d1, symm2_eq hd hnq hl d3, symm2_eq hd hq hnl d2,
      symm2_eq hd hnq hnl d4]

/-- The vertices of a row are pairs of creases of the walk. -/
lemma verts_subset_sym2 {r : Row ι} (hr : r ∈ w.rows) : r.verts ⊆ w.C.sym2 := by
  intro u hu
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, ⟨hq, hg, -, -⟩, rfl⟩ := mem_ttRows.1 hr
    rw [Row.mem_verts_tt] at hu
    rcases hu with rfl | rfl <;> rw [Finset.mk_mem_sym2_iff]
    · exact ⟨hq, hg⟩
    · exact ⟨w.nxt_mem hq, hg⟩
  · obtain ⟨q, l, -, ⟨hq, hl, -, -, -⟩, rfl⟩ := mem_tcRows.1 hr
    rw [Row.mem_verts_tc] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> rw [Finset.mk_mem_sym2_iff]
    · exact ⟨hq, hl⟩
    · exact ⟨w.nxt_mem hq, hl⟩
    · exact ⟨hq, w.nxt_mem hl⟩
    · exact ⟨w.nxt_mem hq, w.nxt_mem hl⟩

/-- Double counting: summing over the rows and their vertices is summing over the pairs,
each weighted by the number of rows that contain it. -/
lemma sum_rows_verts (f : Sym2 ι → ZMod 2) :
    ∑ r ∈ w.rows, ∑ u ∈ r.verts, f u = ∑ u ∈ w.C.sym2, ((w.rowsWith u).card : ZMod 2) * f u := by
  have : ∀ r ∈ w.rows, ∑ u ∈ r.verts, f u = ∑ u ∈ w.C.sym2, if u ∈ r.verts then f u else 0 := by
    intro r hr
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (verts_subset_sym2 hr)]
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [rowsWith, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
  simp

/-- The adjacent pairs of sectors. -/
def adjPairs (w : Walk ι α) : Finset (Sym2 ι) := w.C.image fun k => s(k, nxt w.C k)

lemma mk_nxt_injOn (h3 : 3 ≤ w.C.card) : Set.InjOn (fun k => s(k, nxt w.C k)) w.C := by
  intro a ha b hb h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h1, h2⟩
  · exact h
  · exfalso
    have : nxt w.C (nxt w.C a) = a := by rw [h2]; exact h1.symm
    have := card_le_two_of_nxt_nxt ha this
    omega

lemma mem_adjPairs_iff {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) :
    s(a, b) ∈ w.adjPairs ↔ w.Adj a b := by
  unfold adjPairs Adj
  simp only [Finset.mem_image, Sym2.eq_iff]
  constructor
  · rintro ⟨k, hk, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨b, hb, Or.inr ⟨rfl, rfl⟩⟩

/-- No row contains a pair made of one sector twice. -/
lemma diag_not_mem_verts {r : Row ι} (hr : r ∈ w.rows) (a : ι) : s(a, a) ∉ r.verts := by
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, hqg, rfl⟩ := mem_ttRows.1 hr
    obtain ⟨h1, h2⟩ := tt_distinct hqg
    rw [Row.s_mem_verts_tt]
    rintro (⟨ha, rfl⟩ | ⟨ha, rfl⟩) <;> rcases ha with ha | ha
    all_goals first | exact h1 ha.symm | exact h2 ha.symm
  · obtain ⟨q, l, -, hql, rfl⟩ := mem_tcRows.1 hr
    obtain ⟨d1, d2, d3, d4⟩ := tc_distinct hql
    rw [Row.s_mem_verts_tc]
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;> rcases ha with rfl | rfl <;> rcases hb with h | h
    all_goals first | exact d1 h | exact d2 h | exact d3 h | exact d4 h

/-- The number of rows containing a pair is odd exactly for adjacent pairs. -/
lemma card_rowsWith_mod_two {u : Sym2 ι} (hu : u ∈ w.C.sym2) (h3 : 3 ≤ w.C.card) :
    ((w.rowsWith u).card : ZMod 2) = if u ∈ w.adjPairs then 1 else 0 := by
  induction u using Sym2.ind with
  | _ a b =>
  rw [Finset.mk_mem_sym2_iff] at hu
  obtain ⟨ha, hb⟩ := hu
  by_cases hab : a = b
  · subst hab
    have h0 : w.rowsWith s(a, a) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro r hr
      obtain ⟨hr, hm⟩ := Finset.mem_filter.1 hr
      exact diag_not_mem_verts hr a hm
    have h1 : s(a, a) ∉ w.adjPairs := by
      rw [mem_adjPairs_iff ha ha]
      rintro (h | h) <;> exact w.nxt_ne ha h.symm
    rw [h0, if_neg h1]; rfl
  · rw [card_rowsWith ha hb hab h3]
    simp only [mem_adjPairs_iff ha hb]
    by_cases hov : w.Overlap a b
    · by_cases hadj : w.Adj a b
      · simp [hov, hadj]
      · simp only [hov, hadj, if_true, if_false]; rfl
    · have hadj : ¬ w.Adj a b := fun h => hov (h.elim (fun e => e ▸ overlap_nxt ha)
        (fun e => overlap_comm.1 (e ▸ overlap_nxt hb)))
      simp [hov, hadj]

/-- **Linear part of Theorem 1.**  For `d` symmetric on the sectors, the sum of all the rows
at the vertex, evaluated at `d`, is the sum of `d` over the adjacent pairs. -/
theorem sum_rows_symm {d : ι → ι → ZMod 2} (hd : w.SymmOn d) (h3 : 3 ≤ w.C.card) :
    ∑ r ∈ w.rows, r.eval d = ∑ k ∈ w.C, d k (nxt w.C k) := by
  rw [Finset.sum_congr rfl fun r hr => eval_eq_sum_verts hd hr, sum_rows_verts]
  rw [Finset.sum_congr rfl fun u hu => by rw [card_rowsWith_mod_two hu h3]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, show w.C.sym2.filter (· ∈ w.adjPairs) = w.adjPairs from ?_]
  · unfold adjPairs
    rw [Finset.sum_image (mk_nxt_injOn h3)]
    exact Finset.sum_congr rfl fun k hk => symm2_eq hd hk (w.nxt_mem hk) (w.nxt_ne hk).symm
  · ext u
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    intro hu
    unfold adjPairs at hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hu
    exact Finset.mk_mem_sym2_iff.2 ⟨hk, w.nxt_mem hk⟩

/-- The sum of the rows plus the vertex row does not depend on the layer variables. -/
theorem sum_rows_add_vertex_eq {x y : ι → ι → ZMod 2} (hx : w.Antisymm x) (hy : w.Antisymm y)
    (h3 : 3 ≤ w.C.card) :
    ∑ r ∈ w.rows, r.eval x + ∑ k ∈ w.C, x k (nxt w.C k) =
      ∑ r ∈ w.rows, r.eval y + ∑ k ∈ w.C, y k (nxt w.C k) := by
  have hd : w.SymmOn (x + y) := by
    intro i hi j hj hij
    simp only [Pi.add_apply]
    rw [hx i hi j hj hij, hy i hi j hj hij]
    generalize x i j = a; generalize y i j = b
    revert a b; decide
  have := sum_rows_symm hd h3
  simp only [Row.eval_add, Finset.sum_add_distrib, Pi.add_apply] at this
  generalize ∑ r ∈ w.rows, r.eval x = A at this ⊢
  generalize ∑ r ∈ w.rows, r.eval y = B at this ⊢
  generalize ∑ k ∈ w.C, x k (nxt w.C k) = A' at this ⊢
  generalize ∑ k ∈ w.C, y k (nxt w.C k) = B' at this ⊢
  revert A B A' B'; decide

end Walk

end Origami
