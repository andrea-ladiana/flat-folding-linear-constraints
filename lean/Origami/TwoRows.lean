import Origami.Walk

/-!
# Lemma 2: two rows per pair

Every adjacent pair of sectors lies in exactly one row at the vertex, every other
overlapping pair in exactly two, and a pair that does not overlap in none.

As in the paper, the proof is direct at every walk: the rows containing an overlapping
pair `{a, b}` split into those through the lower ends of the two intervals and those through
the upper ends, and each end contributes exactly one row (a taco–tortilla row if the two
ends differ, a taco–taco row if they coincide on two distinct creases), except the end that
adjacent sectors share.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Row

lemma mem_verts_tt {k k' g : ι} {u : Sym2 ι} :
    u ∈ (tt k k' g).verts ↔ u = s(k, g) ∨ u = s(k', g) := by
  simp [verts, terms]

lemma mem_verts_tc {k k' l l' : ι} {u : Sym2 ι} :
    u ∈ (tc k k' l l').verts ↔ u = s(k, l) ∨ u = s(k', l) ∨ u = s(k, l') ∨ u = s(k', l') := by
  simp [verts, terms]

lemma s_mem_verts_tt {k k' g a b : ι} :
    s(a, b) ∈ (tt k k' g).verts ↔ ((a = k ∨ a = k') ∧ b = g) ∨ ((b = k ∨ b = k') ∧ a = g) := by
  simp only [mem_verts_tt, Sym2.eq_iff]; tauto

lemma s_mem_verts_tc {k k' l l' a b : ι} :
    s(a, b) ∈ (tc k k' l l').verts ↔
      ((a = k ∨ a = k') ∧ (b = l ∨ b = l')) ∨ ((b = k ∨ b = k') ∧ (a = l ∨ a = l')) := by
  simp only [mem_verts_tc, Sym2.eq_iff]; tauto

end Row

namespace Walk

variable {w : Walk ι α}

/-- Two sectors are adjacent if they share a crease. -/
def Adj (w : Walk ι α) (a b : ι) : Prop := b = nxt w.C a ∨ a = nxt w.C b

instance (w : Walk ι α) (a b : ι) : Decidable (w.Adj a b) := by unfold Adj; infer_instance

/-- The rows containing the pair `u`. -/
def rowsWith (w : Walk ι α) (u : Sym2 ι) : Finset (Row ι) := w.rows.filter fun r => u ∈ r.verts

/-- The row through the lower ends of the intervals of `a` and `b`, if any. -/
def lowRows (w : Walk ι α) (a b : ι) : Finset (Row ι) :=
  if w.lo a < w.lo b then {Row.tt (w.lc b) (nxt w.C (w.lc b)) a}
  else if w.lo b < w.lo a then {Row.tt (w.lc a) (nxt w.C (w.lc a)) b}
  else if w.lc a = w.lc b then ∅
  else if w.lc a < w.lc b then {Row.tc (w.lc a) (nxt w.C (w.lc a)) (w.lc b) (nxt w.C (w.lc b))}
  else {Row.tc (w.lc b) (nxt w.C (w.lc b)) (w.lc a) (nxt w.C (w.lc a))}

/-- The row through the upper ends of the intervals of `a` and `b`, if any. -/
def upRows (w : Walk ι α) (a b : ι) : Finset (Row ι) :=
  if w.hi b < w.hi a then {Row.tt (w.uc b) (nxt w.C (w.uc b)) a}
  else if w.hi a < w.hi b then {Row.tt (w.uc a) (nxt w.C (w.uc a)) b}
  else if w.uc a = w.uc b then ∅
  else if w.uc a < w.uc b then {Row.tc (w.uc a) (nxt w.C (w.uc a)) (w.uc b) (nxt w.C (w.uc b))}
  else {Row.tc (w.uc b) (nxt w.C (w.uc b)) (w.uc a) (nxt w.C (w.uc a))}

/-- The sector `g` is one of the two sectors at each of its creases. -/
lemma mem_sectors_lc {g : ι} (hg : g ∈ w.C) : g = w.lc g ∨ g = nxt w.C (w.lc g) := by
  unfold lc; split_ifs
  · exact Or.inr (nxt_prv hg).symm
  · exact Or.inl rfl

lemma mem_sectors_uc {g : ι} (hg : g ∈ w.C) : g = w.uc g ∨ g = nxt w.C (w.uc g) := by
  unfold uc; split_ifs
  · exact Or.inl rfl
  · exact Or.inr (nxt_prv hg).symm

/-- If the sector `t` is one of the two sectors at the crease `q`, then `q` is a crease of `t`. -/
lemma crease_of_sector {t q : ι} (ht : t ∈ w.C) (hq : q ∈ w.C) (h : t = q ∨ t = nxt w.C q) :
    q = t ∨ q = prv w.C t := (sector_at_iff ht hq).1 h

lemma s_mem_tt_of {q g a b : ι} (h : (a = q ∨ a = nxt w.C q) ∧ b = g) :
    s(a, b) ∈ (Row.tt q (nxt w.C q) g).verts := by
  rw [Row.mem_verts_tt]
  rcases h with ⟨rfl | rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma s_mem_tt_of' {q g a b : ι} (h : (b = q ∨ b = nxt w.C q) ∧ a = g) :
    s(a, b) ∈ (Row.tt q (nxt w.C q) g).verts := by
  rw [Sym2.eq_swap]; exact s_mem_tt_of h

lemma s_mem_tc_of {q l a b : ι} (h : (a = q ∨ a = nxt w.C q) ∧ (b = l ∨ b = nxt w.C l)) :
    s(a, b) ∈ (Row.tc q (nxt w.C q) l (nxt w.C l)).verts := by
  rw [Row.mem_verts_tc]
  rcases h with ⟨rfl | rfl, rfl | rfl⟩ <;> simp

lemma s_mem_tc_of' {q l a b : ι} (h : (b = q ∨ b = nxt w.C q) ∧ (a = l ∨ a = nxt w.C l)) :
    s(a, b) ∈ (Row.tc q (nxt w.C q) l (nxt w.C l)).verts := by
  rw [Sym2.eq_swap]; exact s_mem_tc_of h

lemma overlap_comm {a b : ι} : w.Overlap a b ↔ w.Overlap b a := by
  unfold Overlap; rw [max_comm, min_comm]

/-- Every vertex of a row is an overlapping pair. -/
lemma overlap_of_mem_verts {r : Row ι} (hr : r ∈ w.rows) {a b : ι} (hab : s(a, b) ∈ r.verts) :
    w.Overlap a b := by
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, ⟨hq, hg, h1, h2⟩, rfl⟩ := mem_ttRows.1 hr
    -- the taco sector `t` has the crease `q` as an end
    have key : ∀ t, (t = q ∨ t = nxt w.C q) → w.Overlap t g := by
      intro t ht
      have htC : t ∈ w.C := by rcases ht with rfl | rfl <;> [exact hq; exact w.nxt_mem hq]
      have hqt := crease_of_sector htC hq ht
      unfold Overlap
      by_cases hu : w.up q
      · have := eq_uc_of_up htC hqt hu
        have hc : w.hi t = w.c q := by rw [← c_uc htC, ← this]
        have := lo_lt_hi htC
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        refine ⟨⟨by linarith, by linarith⟩, by linarith [lo_lt_hi hg], by linarith⟩
      · have := eq_lc_of_not_up htC hqt hu
        have hc : w.lo t = w.c q := by rw [← c_lc htC, ← this]
        have := lo_lt_hi htC
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        refine ⟨⟨by linarith, by linarith⟩, by linarith [lo_lt_hi hg], by linarith⟩
    rw [Row.s_mem_verts_tt] at hab
    rcases hab with ⟨ha, rfl⟩ | ⟨hb, rfl⟩
    · exact key _ ha
    · exact overlap_comm.1 (key _ hb)
  · obtain ⟨q, l, -, ⟨hq, hl, -, heq, hup⟩, rfl⟩ := mem_tcRows.1 hr
    -- all four sectors end at the common position, on the same side
    have key : ∀ t, (t = q ∨ t = nxt w.C q) → ∀ t', (t' = l ∨ t' = nxt w.C l) →
        w.Overlap t t' := by
      intro t ht t' ht'
      have htC : t ∈ w.C := by rcases ht with rfl | rfl <;> [exact hq; exact w.nxt_mem hq]
      have htC' : t' ∈ w.C := by rcases ht' with rfl | rfl <;> [exact hl; exact w.nxt_mem hl]
      have hqt := crease_of_sector htC hq ht
      have hlt := crease_of_sector htC' hl ht'
      unfold Overlap
      have h1 := lo_lt_hi htC
      have h2 := lo_lt_hi htC'
      by_cases hu : w.up q
      · have e1 := eq_uc_of_up htC hqt hu
        have e2 := eq_uc_of_up htC' hlt (hup.1 hu)
        have c1 : w.hi t = w.c q := by rw [← c_uc htC, ← e1]
        have c2 : w.hi t' = w.c l := by rw [← c_uc htC', ← e2]
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      · have e1 := eq_lc_of_not_up htC hqt hu
        have e2 := eq_lc_of_not_up htC' hlt (fun h => hu (hup.2 h))
        have c1 : w.lo t = w.c q := by rw [← c_lc htC, ← e1]
        have c2 : w.lo t' = w.c l := by rw [← c_lc htC', ← e2]
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    rw [Row.s_mem_verts_tc] at hab
    rcases hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact key _ ha _ hb
    · exact overlap_comm.1 (key _ hb _ ha)


lemma overlap_facts {a b : ι} (h : w.Overlap a b) : w.lo a < w.hi b ∧ w.lo b < w.hi a := by
  unfold Overlap at h
  rw [max_lt_iff, lt_min_iff, lt_min_iff] at h
  exact ⟨h.1.2, h.2.1⟩

lemma tt_mem_rows {q g : ι} (h : w.IsTT q g) : Row.tt q (nxt w.C q) g ∈ w.rows :=
  mem_rows.2 (Or.inl (mem_ttRows.2 ⟨q, g, h, rfl⟩))

lemma tc_mem_rows {q l : ι} (hql : q < l) (h : w.IsTC q l) :
    Row.tc q (nxt w.C q) l (nxt w.C l) ∈ w.rows :=
  mem_rows.2 (Or.inr (mem_tcRows.2 ⟨q, l, hql, h, rfl⟩))

/-- The candidate rows are rows containing the pair. -/
lemma lowRows_subset {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hov : w.Overlap a b) :
    w.lowRows a b ⊆ w.rowsWith s(a, b) := by
  obtain ⟨h1, h2⟩ := overlap_facts hov
  intro r hr
  unfold lowRows at hr
  unfold rowsWith; rw [Finset.mem_filter]
  split_ifs at hr with c1 c2 c3 c4 <;> simp only [Finset.mem_singleton,
    Finset.notMem_empty] at hr <;> subst hr
  · refine ⟨tt_mem_rows ⟨lc_mem hb, ha, by rw [c_lc hb]; exact c1, by rw [c_lc hb]; exact h2⟩, ?_⟩
    exact s_mem_tt_of' ⟨mem_sectors_lc hb, rfl⟩
  · refine ⟨tt_mem_rows ⟨lc_mem ha, hb, by rw [c_lc ha]; exact c2, by rw [c_lc ha]; exact h1⟩, ?_⟩
    exact s_mem_tt_of ⟨mem_sectors_lc ha, rfl⟩
  · have heq : w.lo a = w.lo b := le_antisymm (not_lt.1 c2) (not_lt.1 c1)
    refine ⟨tc_mem_rows c4 ⟨lc_mem ha, lc_mem hb, c3, by rw [c_lc ha, c_lc hb, heq], ?_⟩, ?_⟩
    · simp [not_up_lc ha, not_up_lc hb]
    · exact s_mem_tc_of ⟨mem_sectors_lc ha, mem_sectors_lc hb⟩
  · have heq : w.lo a = w.lo b := le_antisymm (not_lt.1 c2) (not_lt.1 c1)
    have c5 : w.lc b < w.lc a := lt_of_le_of_ne (not_lt.1 c4) (Ne.symm c3)
    refine ⟨tc_mem_rows c5 ⟨lc_mem hb, lc_mem ha, Ne.symm c3, by rw [c_lc ha, c_lc hb, heq], ?_⟩,
      ?_⟩
    · simp [not_up_lc ha, not_up_lc hb]
    · exact s_mem_tc_of' ⟨mem_sectors_lc hb, mem_sectors_lc ha⟩

lemma upRows_subset {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hov : w.Overlap a b) :
    w.upRows a b ⊆ w.rowsWith s(a, b) := by
  obtain ⟨h1, h2⟩ := overlap_facts hov
  intro r hr
  unfold upRows at hr
  unfold rowsWith; rw [Finset.mem_filter]
  split_ifs at hr with c1 c2 c3 c4 <;> simp only [Finset.mem_singleton,
    Finset.notMem_empty] at hr <;> subst hr
  · refine ⟨tt_mem_rows ⟨uc_mem hb, ha, by rw [c_uc hb]; exact h1, by rw [c_uc hb]; exact c1⟩, ?_⟩
    exact s_mem_tt_of' ⟨mem_sectors_uc hb, rfl⟩
  · refine ⟨tt_mem_rows ⟨uc_mem ha, hb, by rw [c_uc ha]; exact h2, by rw [c_uc ha]; exact c2⟩, ?_⟩
    exact s_mem_tt_of ⟨mem_sectors_uc ha, rfl⟩
  · have heq : w.hi a = w.hi b := le_antisymm (not_lt.1 c1) (not_lt.1 c2)
    refine ⟨tc_mem_rows c4 ⟨uc_mem ha, uc_mem hb, c3, by rw [c_uc ha, c_uc hb, heq], ?_⟩, ?_⟩
    · simp [up_uc ha, up_uc hb]
    · exact s_mem_tc_of ⟨mem_sectors_uc ha, mem_sectors_uc hb⟩
  · have heq : w.hi a = w.hi b := le_antisymm (not_lt.1 c1) (not_lt.1 c2)
    have c5 : w.uc b < w.uc a := lt_of_le_of_ne (not_lt.1 c4) (Ne.symm c3)
    refine ⟨tc_mem_rows c5 ⟨uc_mem hb, uc_mem ha, Ne.symm c3, by rw [c_uc ha, c_uc hb, heq], ?_⟩,
      ?_⟩
    · simp [up_uc ha, up_uc hb]
    · exact s_mem_tc_of' ⟨mem_sectors_uc hb, mem_sectors_uc ha⟩

/-- Conversely, every row containing the pair is one of the candidates. -/
lemma rowsWith_subset {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) :
    w.rowsWith s(a, b) ⊆ w.lowRows a b ∪ w.upRows a b := by
  intro r hr
  unfold rowsWith at hr
  obtain ⟨hr, hab⟩ := Finset.mem_filter.1 hr
  rw [Finset.mem_union]
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, ⟨hq, hg, i1, i2⟩, rfl⟩ := mem_ttRows.1 hr
    rw [Row.s_mem_verts_tt] at hab
    rcases hab with ⟨hat, rfl⟩ | ⟨hbt, rfl⟩
    · have hqa := crease_of_sector ha hq hat
      by_cases hu : w.up q
      · have e := eq_uc_of_up ha hqa hu
        have c := c_uc ha; rw [← e] at c
        right; unfold upRows
        rw [if_neg (by rw [← c]; exact not_lt.2 i2.le), if_pos (by rw [← c]; exact i2), e]
        exact Finset.mem_singleton_self _
      · have e := eq_lc_of_not_up ha hqa hu
        have c := c_lc ha; rw [← e] at c
        left; unfold lowRows
        rw [if_neg (by rw [← c]; exact not_lt.2 i1.le), if_pos (by rw [← c]; exact i1), e]
        exact Finset.mem_singleton_self _
    · have hqb := crease_of_sector hb hq hbt
      by_cases hu : w.up q
      · have e := eq_uc_of_up hb hqb hu
        have c := c_uc hb; rw [← e] at c
        right; unfold upRows
        rw [if_pos (by rw [← c]; exact i2), e]
        exact Finset.mem_singleton_self _
      · have e := eq_lc_of_not_up hb hqb hu
        have c := c_lc hb; rw [← e] at c
        left; unfold lowRows
        rw [if_pos (by rw [← c]; exact i1), e]
        exact Finset.mem_singleton_self _
  · obtain ⟨q, l, hql, ⟨hq, hl, hne, heq, hup⟩, rfl⟩ := mem_tcRows.1 hr
    rw [Row.s_mem_verts_tc] at hab
    rcases hab with ⟨hat, hbt⟩ | ⟨hbt, hat⟩
    · have hqa := crease_of_sector ha hq hat
      have hlb := crease_of_sector hb hl hbt
      by_cases hu : w.up q
      · have e1 := eq_uc_of_up ha hqa hu
        have e2 := eq_uc_of_up hb hlb (hup.1 hu)
        have c1 := c_uc ha; rw [← e1] at c1
        have c2 := c_uc hb; rw [← e2] at c2
        right; unfold upRows
        rw [if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _),
          if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _), if_neg (by rw [← e1, ← e2]; exact hne),
          if_pos (by rw [← e1, ← e2]; exact hql), ← e1, ← e2]
        exact Finset.mem_singleton_self _
      · have e1 := eq_lc_of_not_up ha hqa hu
        have e2 := eq_lc_of_not_up hb hlb (fun h => hu (hup.2 h))
        have c1 := c_lc ha; rw [← e1] at c1
        have c2 := c_lc hb; rw [← e2] at c2
        left; unfold lowRows
        rw [if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _),
          if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _), if_neg (by rw [← e1, ← e2]; exact hne),
          if_pos (by rw [← e1, ← e2]; exact hql), ← e1, ← e2]
        exact Finset.mem_singleton_self _
    · have hqb := crease_of_sector hb hq hbt
      have hla := crease_of_sector ha hl hat
      by_cases hu : w.up q
      · have e1 := eq_uc_of_up hb hqb hu
        have e2 := eq_uc_of_up ha hla (hup.1 hu)
        have c1 := c_uc hb; rw [← e1] at c1
        have c2 := c_uc ha; rw [← e2] at c2
        right; unfold upRows
        rw [if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _),
          if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _),
          if_neg (by rw [← e1, ← e2]; exact Ne.symm hne),
          if_neg (by rw [← e1, ← e2]; exact not_lt.2 hql.le), ← e1, ← e2]
        exact Finset.mem_singleton_self _
      · have e1 := eq_lc_of_not_up hb hqb hu
        have e2 := eq_lc_of_not_up ha hla (fun h => hu (hup.2 h))
        have c1 := c_lc hb; rw [← e1] at c1
        have c2 := c_lc ha; rw [← e2] at c2
        left; unfold lowRows
        rw [if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _),
          if_neg (by rw [← c1, ← c2, heq]; exact lt_irrefl _),
          if_neg (by rw [← e1, ← e2]; exact Ne.symm hne),
          if_neg (by rw [← e1, ← e2]; exact not_lt.2 hql.le), ← e1, ← e2]
        exact Finset.mem_singleton_self _

lemma rowsWith_eq {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hov : w.Overlap a b) :
    w.rowsWith s(a, b) = w.lowRows a b ∪ w.upRows a b :=
  le_antisymm (rowsWith_subset ha hb)
    (Finset.union_subset (lowRows_subset ha hb hov) (upRows_subset ha hb hov))

lemma card_lowRows {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) :
    (w.lowRows a b).card = if w.lc a = w.lc b then 0 else 1 := by
  by_cases hl : w.lc a = w.lc b
  · have he : w.lo a = w.lo b := by rw [← c_lc ha, ← c_lc hb, hl]
    simp [lowRows, he, hl]
  · simp only [hl, if_false]
    unfold lowRows
    split_ifs <;> simp_all

lemma card_upRows {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) :
    (w.upRows a b).card = if w.uc a = w.uc b then 0 else 1 := by
  by_cases hl : w.uc a = w.uc b
  · have he : w.hi a = w.hi b := by rw [← c_uc ha, ← c_uc hb, hl]
    simp [upRows, he, hl]
  · simp only [hl, if_false]
    unfold upRows
    split_ifs <;> simp_all

/-- Rows through lower ends start at a minimum, rows through upper ends at a maximum. -/
lemma disjoint_low_up {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) :
    Disjoint (w.lowRows a b) (w.upRows a b) := by
  rw [Finset.disjoint_left]
  intro r h1 h2
  have hl : (∃ q, ¬ w.up q ∧ ∃ k' g, r = Row.tt q k' g) ∨
      (∃ q, ¬ w.up q ∧ ∃ k' l l', r = Row.tc q k' l l') := by
    unfold lowRows at h1
    split_ifs at h1 <;> simp only [Finset.mem_singleton, Finset.notMem_empty] at h1 <;> subst h1
    · exact Or.inl ⟨_, not_up_lc hb, _, _, rfl⟩
    · exact Or.inl ⟨_, not_up_lc ha, _, _, rfl⟩
    · exact Or.inr ⟨_, not_up_lc ha, _, _, _, rfl⟩
    · exact Or.inr ⟨_, not_up_lc hb, _, _, _, rfl⟩
  have hu : (∃ q, w.up q ∧ ∃ k' g, r = Row.tt q k' g) ∨
      (∃ q, w.up q ∧ ∃ k' l l', r = Row.tc q k' l l') := by
    unfold upRows at h2
    split_ifs at h2 <;> simp only [Finset.mem_singleton, Finset.notMem_empty] at h2 <;> subst h2
    · exact Or.inl ⟨_, up_uc hb, _, _, rfl⟩
    · exact Or.inl ⟨_, up_uc ha, _, _, rfl⟩
    · exact Or.inr ⟨_, up_uc ha, _, _, _, rfl⟩
    · exact Or.inr ⟨_, up_uc hb, _, _, _, rfl⟩
  rcases hl with ⟨q, hq, k', g, rfl⟩ | ⟨q, hq, k', l, l', rfl⟩ <;>
    rcases hu with ⟨q', hq', k'', g', h⟩ | ⟨q', hq', k'', l'', l''', h⟩ <;>
    simp only [Row.tt.injEq, Row.tc.injEq, reduceCtorEq] at h
  · exact hq (h.1 ▸ hq')
  · exact hq (h.1 ▸ hq')

/-- Two distinct sectors share a lower or an upper crease exactly when they are adjacent. -/
lemma share_iff_adj {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hab : a ≠ b) :
    (w.lc a = w.lc b ∨ w.uc a = w.uc b) ↔ w.Adj a b := by
  have hcr : ∀ q, q = w.lc a ∨ q = w.uc a ↔ q = a ∨ q = prv w.C a := fun q => by
    unfold lc uc; split_ifs <;> tauto
  have hcr' : ∀ q, q = w.lc b ∨ q = w.uc b ↔ q = b ∨ q = prv w.C b := fun q => by
    unfold lc uc; split_ifs <;> tauto
  constructor
  · intro h
    obtain ⟨q, hqa, hqb⟩ : ∃ q, (q = a ∨ q = prv w.C a) ∧ (q = b ∨ q = prv w.C b) := by
      rcases h with h | h
      · exact ⟨w.lc a, (hcr _).1 (Or.inl rfl), (hcr' _).1 (Or.inl h)⟩
      · exact ⟨w.uc a, (hcr _).1 (Or.inr rfl), (hcr' _).1 (Or.inr h)⟩
    unfold Adj
    rcases hqa with rfl | rfl <;> rcases hqb with h | h
    · exact absurd h hab
    · left; rw [h, nxt_prv hb]
    · right; rw [← h, nxt_prv ha]
    · exact absurd (prv_injOn ha hb h) hab
  · rintro (rfl | rfl)
    · have h1 : a = a ∨ a = prv w.C a := Or.inl rfl
      have h2 : a = nxt w.C a ∨ a = prv w.C (nxt w.C a) := Or.inr (prv_nxt ha).symm
      by_cases hu : w.up a
      · right; rw [← eq_uc_of_up ha h1 hu, ← eq_uc_of_up hb h2 hu]
      · left; rw [← eq_lc_of_not_up ha h1 hu, ← eq_lc_of_not_up hb h2 hu]
    · have h1 : b = b ∨ b = prv w.C b := Or.inl rfl
      have h2 : b = nxt w.C b ∨ b = prv w.C (nxt w.C b) := Or.inr (prv_nxt hb).symm
      by_cases hu : w.up b
      · right; rw [← eq_uc_of_up ha h2 hu, ← eq_uc_of_up hb h1 hu]
      · left; rw [← eq_lc_of_not_up ha h2 hu, ← eq_lc_of_not_up hb h1 hu]

lemma not_share_both {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hab : a ≠ b)
    (h3 : 3 ≤ w.C.card) : ¬ (w.lc a = w.lc b ∧ w.uc a = w.uc b) := by
  rintro ⟨h1, h2⟩
  have e1 : (w.lc a = a ∨ w.lc a = prv w.C a) := by unfold lc; split_ifs <;> simp
  have e2 : (w.uc a = a ∨ w.uc a = prv w.C a) := by unfold uc; split_ifs <;> simp
  have f1 : (w.lc b = b ∨ w.lc b = prv w.C b) := by unfold lc; split_ifs <;> simp
  have f2 : (w.uc b = b ∨ w.uc b = prv w.C b) := by unfold uc; split_ifs <;> simp
  have hne := lc_ne_uc ha
  have hne' := lc_ne_uc hb
  have key : a = prv w.C b ∧ b = prv w.C a := by
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases f1 with f1 | f1 <;>
      rcases f2 with f2 | f2
    all_goals first
      | exact absurd (e1.trans e2.symm) hne
      | exact absurd (f1.trans f2.symm) hne'
      | exact absurd (e1.symm.trans (h1.trans f1)) hab
      | exact absurd (e2.symm.trans (h2.trans f2)) hab
      | exact absurd (prv_injOn ha hb (e1.symm.trans (h1.trans f1))) hab
      | exact absurd (prv_injOn ha hb (e2.symm.trans (h2.trans f2))) hab
      | exact ⟨e1.symm.trans (h1.trans f1), (f2.symm.trans (h2.symm.trans e2))⟩
      | exact ⟨e2.symm.trans (h2.trans f2), (f1.symm.trans (h1.symm.trans e1))⟩
  have : nxt w.C (nxt w.C a) = a := by
    rw [show nxt w.C a = b by rw [key.1, nxt_prv hb], key.2, nxt_prv ha]
  have := card_le_two_of_nxt_nxt ha this
  omega

/-- **Lemma 2 (two rows per pair).**  At a walk with at least three creases, an adjacent pair
of sectors lies in exactly one row, a non-adjacent overlapping pair in exactly two, and a
pair that does not overlap in none. -/
theorem card_rowsWith {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hab : a ≠ b)
    (h3 : 3 ≤ w.C.card) :
    (w.rowsWith s(a, b)).card = if w.Overlap a b then (if w.Adj a b then 1 else 2) else 0 := by
  split_ifs with hov hadj hadj
  · rw [rowsWith_eq ha hb hov, Finset.card_union_of_disjoint (disjoint_low_up ha hb),
      card_lowRows ha hb, card_upRows ha hb]
    have h1 := (share_iff_adj ha hb hab).2 hadj
    have h2 := not_share_both ha hb hab h3
    split_ifs <;> tauto
  · rw [rowsWith_eq ha hb hov, Finset.card_union_of_disjoint (disjoint_low_up ha hb),
      card_lowRows ha hb, card_upRows ha hb]
    have h1 := fun h => hadj ((share_iff_adj ha hb hab).1 h)
    split_ifs <;> tauto
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro r hr
    unfold rowsWith at hr
    obtain ⟨hr, hm⟩ := Finset.mem_filter.1 hr
    exact hov (overlap_of_mem_verts hr hm)

/-- Adjacent sectors overlap. -/
lemma overlap_nxt {a : ι} (ha : a ∈ w.C) : w.Overlap a (nxt w.C a) := by
  have hb := w.nxt_mem ha
  have h1 : a = a ∨ a = prv w.C a := Or.inl rfl
  have h2 : a = nxt w.C a ∨ a = prv w.C (nxt w.C a) := Or.inr (prv_nxt ha).symm
  have l1 := lo_lt_hi ha
  have l2 := lo_lt_hi hb
  unfold Overlap
  rw [max_lt_iff, lt_min_iff, lt_min_iff]
  by_cases hu : w.up a
  · have e1 := c_uc ha; rw [← eq_uc_of_up ha h1 hu] at e1
    have e2 := c_uc hb; rw [← eq_uc_of_up hb h2 hu] at e2
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · have e1 := c_lc ha; rw [← eq_lc_of_not_up ha h1 hu] at e1
    have e2 := c_lc hb; rw [← eq_lc_of_not_up hb h2 hu] at e2
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end Walk

end Origami
