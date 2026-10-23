import Origami.Generic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order

/-!
# Flat-folded states and perturbations; Maekawa's theorem (Proposition 3, Corollary 3)

Given a flat-folded state `h` of a vertex, we move the creases of each ray apart, keeping the
order of distinct positions, putting maxima before minima (so that their sectors, which point
in opposite directions, do not start to overlap), and ordering the creases of one ray and one
type by the size of their tacos in the stack: inner tacos move into the sectors of the outer
ones.  The new positions are the ranks of the creases for the lexicographic key

  (position, type, ± size of the taco, name),

so the perturbed walk is generic.  The state `h` satisfies all its taco–tortilla rows
(Proposition 3): the only new rows split taco–taco rows of the vertex, and they hold because
two tacos on one ray are nested or stacked.  Theorem 2 then gives Maekawa's theorem for every
flat-folded state (Corollary 3), using transitivity only through the stacking order.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Walk

variable {w : Walk ι α}

/-- The key ordering the creases of the perturbation. -/
def pkey (w : Walk ι α) (h : ι → ℤ) (k : ι) : α ×ₗ (ℕ ×ₗ (ℤ ×ₗ ι)) :=
  toLex (w.c k, toLex ((if w.up k then 0 else 1 : ℕ),
    toLex ((if w.up k then 1 else -1) * |h k - h (nxt w.C k)|, k)))

lemma pkey_lt_of_c_lt (h : ι → ℤ) {q l : ι} (hc : w.c q < w.c l) : w.pkey h q < w.pkey h l :=
  Prod.Lex.toLex_lt_toLex.2 (Or.inl hc)

lemma c_le_of_pkey_lt (h : ι → ℤ) {q l : ι} (hk : w.pkey h q < w.pkey h l) : w.c q ≤ w.c l := by
  rcases Prod.Lex.toLex_lt_toLex.1 hk with h1 | ⟨h1, -⟩
  · exact h1.le
  · exact h1.le

lemma pkey_injective (h : ι → ℤ) {q l : ι} (he : w.pkey h q = w.pkey h l) : q = l := by
  unfold pkey at he
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at he
  exact he.2.2.2

/-- The new position: the rank of the key among the creases. -/
noncomputable def prank (w : Walk ι α) (h : ι → ℤ) (k : ι) : ℕ :=
  (w.C.filter fun j => w.pkey h j < w.pkey h k).card

lemma prank_lt (h : ι → ℤ) {q l : ι} (hq : q ∈ w.C) (hl : w.pkey h q < w.pkey h l) :
    w.prank h q < w.prank h l := by
  apply Finset.card_lt_card
  refine ⟨fun j hj => ?_, fun hs => ?_⟩
  · simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.trans hl⟩
  · have := hs (Finset.mem_filter.2 ⟨hq, hl⟩)
    simp at this

lemma prank_lt_iff (h : ι → ℤ) {q l : ι} (hq : q ∈ w.C) (hl : l ∈ w.C) :
    w.prank h q < w.prank h l ↔ w.pkey h q < w.pkey h l := by
  refine ⟨fun hr => ?_, prank_lt h hq⟩
  by_contra hk
  rcases lt_or_eq_of_le (not_lt.1 hk) with h1 | h1
  · exact absurd (prank_lt h hl h1) (not_lt.2 hr.le)
  · rw [pkey_injective h h1] at hr; exact lt_irrefl _ hr

/-- **The perturbed walk.** -/
noncomputable def perturb (w : Walk ι α) (h : ι → ℤ) : Walk ι ℚ where
  C := w.C
  c := fun k => (w.prank h k : ℚ)
  two_le := w.two_le
  zig := by
    intro k hk
    have hp := w.prv_mem hk; have hn := w.nxt_mem hk
    rcases w.zig k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨Nat.cast_lt.2 (prank_lt h hp (pkey_lt_of_c_lt h h1)),
        Nat.cast_lt.2 (prank_lt h hn (pkey_lt_of_c_lt h h2))⟩
    · right
      exact ⟨Nat.cast_lt.2 (prank_lt h hk (pkey_lt_of_c_lt h h1)),
        Nat.cast_lt.2 (prank_lt h hk (pkey_lt_of_c_lt h h2))⟩

@[simp] lemma perturb_C (h : ι → ℤ) : (w.perturb h).C = w.C := rfl

lemma perturb_lt (h : ι → ℤ) {q l : ι} (hq : q ∈ w.C) (hl : l ∈ w.C) :
    (w.perturb h).c q < (w.perturb h).c l ↔ w.pkey h q < w.pkey h l := by
  show (w.prank h q : ℚ) < w.prank h l ↔ _
  rw [Nat.cast_lt]; exact prank_lt_iff h hq hl

/-- The perturbation keeps every maximum a maximum and every minimum a minimum. -/
lemma perturb_up (h : ι → ℤ) {k : ι} (hk : k ∈ w.C) : (w.perturb h).up k ↔ w.up k := by
  unfold up
  rw [perturb_C, perturb_lt h (w.prv_mem hk) hk]
  constructor
  · intro hl
    rcases lt_or_gt_of_ne (c_prv_ne hk) with h1 | h1
    · exact h1
    · exact absurd hl (not_lt.2 (pkey_lt_of_c_lt h h1).le)
  · exact pkey_lt_of_c_lt h

/-- The perturbation is generic. -/
lemma perturb_generic (h : ι → ℤ) : (w.perturb h).Generic := by
  intro q hq l hl he
  by_contra hne
  have he' : w.prank h q = w.prank h l := by
    have : (w.prank h q : ℚ) = w.prank h l := he
    exact_mod_cast this
  have hk : w.pkey h q ≠ w.pkey h l := fun e => hne (pkey_injective h e)
  rcases lt_or_gt_of_ne hk with h1 | h1
  · exact absurd he' (ne_of_lt (prank_lt h hq h1))
  · exact absurd he'.symm (ne_of_lt (prank_lt h hl h1))

/-- The perturbation keeps the order of distinct positions. -/
lemma perturb_strict (h : ι → ℤ) {q l : ι} (hq : q ∈ w.C) (hl : l ∈ w.C) (hc : w.c q < w.c l) :
    (w.perturb h).c q < (w.perturb h).c l :=
  (perturb_lt h hq hl).2 (pkey_lt_of_c_lt h hc)

/-- On a ray where a maximum and a minimum coincide, the minimum moves to the right. -/
lemma perturb_max_min (h : ι → ℤ) {q l : ι} (hq : q ∈ w.C) (hl : l ∈ w.C) (hc : w.c q = w.c l)
    (huq : w.up q) (hul : ¬ w.up l) : (w.perturb h).c q < (w.perturb h).c l := by
  rw [perturb_lt h hq hl]
  apply Prod.Lex.toLex_lt_toLex.2
  right
  refine ⟨hc, Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)⟩
  simp [huq, hul]

lemma perturb_lc (h : ι → ℤ) {g : ι} (hg : g ∈ w.C) : (w.perturb h).lc g = w.lc g := by
  unfold lc; simp only [perturb_C, perturb_up h hg]

lemma perturb_uc (h : ι → ℤ) {g : ι} (hg : g ∈ w.C) : (w.perturb h).uc g = w.uc g := by
  unfold uc; simp only [perturb_C, perturb_up h hg]

/-- Every taco–tortilla row of the vertex is a row of the perturbation. -/
lemma ttRows_subset_perturb (h : ι → ℤ) : w.ttRows ⊆ (w.perturb h).ttRows := by
  intro r hr
  obtain ⟨q, g, ⟨hq, hg, i1, i2⟩, rfl⟩ := mem_ttRows.1 hr
  refine mem_ttRows.2 ⟨q, g, ⟨hq, hg, ?_, ?_⟩, rfl⟩
  · rw [← c_lc (w := w.perturb h) hg, perturb_lc h hg]
    exact perturb_strict h (lc_mem hg) hq (by rw [c_lc hg]; exact i1)
  · rw [← c_uc (w := w.perturb h) hg, perturb_uc h hg]
    exact perturb_strict h hq (uc_mem hg) (by rw [c_uc hg]; exact i2)

/-! ### Proposition 3 -/

/-- The layer `g` lies strictly between the layers `a` and `b`. -/
def Btw (h : ι → ℤ) (a b g : ι) : Prop := (h a < h g ∧ h g < h b) ∨ (h b < h g ∧ h g < h a)

lemma xOf_add_xOf (h : ι → ℤ) {a b g : ι} (hag : h a ≠ h g) (hbg : h b ≠ h g) :
    xOf h a g + xOf h b g = if Btw h a b g then 1 else 0 := by
  unfold xOf Btw
  rcases lt_or_gt_of_ne hag with h1 | h1 <;> rcases lt_or_gt_of_ne hbg with h2 | h2
  · rw [if_pos h1, if_pos h2, if_neg (by omega)]; decide
  · rw [if_pos h1, if_neg (not_lt.2 h2.le), if_pos (Or.inl ⟨h1, h2⟩)]; rfl
  · rw [if_neg (not_lt.2 h1.le), if_pos h2, if_pos (Or.inr ⟨h2, h1⟩)]; rfl
  · rw [if_neg (not_lt.2 h1.le), if_neg (not_lt.2 h2.le), if_neg (by omega)]; rfl

/-- The taco–taco row of two creases on one ray, in either order. -/
lemma tc_holds {h : ι → ℤ} (hf : w.IsFlat h) {q u : ι} (htc : w.IsTC q u) :
    xOf h q u + xOf h (nxt w.C q) u + xOf h q (nxt w.C u) + xOf h (nxt w.C q) (nxt w.C u) = 0 := by
  have hx := antisymm_xOf (w := w) hf.1
  rcases lt_or_gt_of_ne htc.2.2.1 with hlt | hlt
  · have := hf.2 _ (tc_mem_rows hlt htc); rwa [Row.eval_tc] at this
  · have htc' : w.IsTC u q := ⟨htc.2.1, htc.1, htc.2.2.1.symm, htc.2.2.2.1.symm, htc.2.2.2.2.symm⟩
    have := hf.2 _ (tc_mem_rows hlt htc')
    rw [Row.eval_tc] at this
    obtain ⟨d1, d2, d3, d4⟩ := tc_distinct htc
    have hq := htc.1; have hu := htc.2.1
    rw [hx _ hq _ hu d1, hx _ hq _ (w.nxt_mem hu) d2, hx _ (w.nxt_mem hq) _ hu d3,
      hx _ (w.nxt_mem hq) _ (w.nxt_mem hu) d4] at this
    revert this
    generalize xOf h q u = a; generalize xOf h q (nxt w.C u) = b
    generalize xOf h (nxt w.C q) u = c; generalize xOf h (nxt w.C q) (nxt w.C u) = d
    revert a b c d; decide

/-- **The split row holds.**  If the taco of `q` is not larger than the taco of `u`, on the same
ray and of the same type, then neither sector at `u` lies inside the taco of `q`. -/
lemma split_row {h : ι → ℤ} (hf : w.IsFlat h) {q u g : ι} (htc : w.IsTC q u)
    (hg : g = u ∨ g = nxt w.C u) (hle : |h q - h (nxt w.C q)| ≤ |h u - h (nxt w.C u)|) :
    xOf h q g + xOf h (nxt w.C q) g = 0 := by
  obtain ⟨d1, d2, d3, d4⟩ := tc_distinct htc
  have hq := htc.1; have hu := htc.2.1
  have hnq := w.nxt_mem hq; have hnu := w.nxt_mem hu
  have inj : ∀ {a b}, a ∈ w.C → b ∈ w.C → a ≠ b → h a ≠ h b := fun ha hb hab e => hab (hf.1 ha hb e)
  have t := tc_holds hf htc
  rw [add_assoc, xOf_add_xOf h (inj hq hnu d2) (inj hnq hnu d4)] at t
  rw [xOf_add_xOf h (inj hq hu d1) (inj hnq hu d3)] at t
  -- `u` and `nxt u` are both inside the taco of `q`, or both outside
  have hboth : Btw h q (nxt w.C q) u ↔ Btw h q (nxt w.C q) (nxt w.C u) := by
    revert t; split_ifs <;> simp_all
  have hgC : g ∈ w.C := by rcases hg with rfl | rfl <;> assumption
  have hgq : q ≠ g := by rcases hg with rfl | rfl <;> assumption
  have hgnq : nxt w.C q ≠ g := by rcases hg with rfl | rfl <;> assumption
  rw [xOf_add_xOf h (inj hq hgC hgq) (inj hnq hgC hgnq), if_neg]
  intro hb
  have hb' : Btw h q (nxt w.C q) u ∧ Btw h q (nxt w.C q) (nxt w.C u) := by
    rcases hg with rfl | rfl
    · exact ⟨hb, hboth.1 hb⟩
    · exact ⟨hboth.2 hb, hb⟩
  obtain ⟨b1, b2⟩ := hb'
  unfold Btw at b1 b2
  have hlt : |h u - h (nxt w.C u)| < |h q - h (nxt w.C q)| := by
    rcases b1 with ⟨b1, b1'⟩ | ⟨b1, b1'⟩ <;> rcases b2 with ⟨b2, b2'⟩ | ⟨b2, b2'⟩ <;>
      rw [abs_lt] <;> constructor <;>
      first
      | (rw [abs_of_neg (by linarith)]; linarith)
      | (rw [abs_of_pos (by linarith)]; linarith)
  linarith

/-- **Proposition 3 (flat-folded states and perturbations).**  Every flat-folded state of a
vertex satisfies the taco–tortilla rows of an admissible perturbation of the vertex. -/
theorem prop2 {h : ι → ℤ} (hf : w.IsFlat h) : ∀ r ∈ (w.perturb h).ttRows, r.eval (xOf h) = 0 := by
  intro r hr
  obtain ⟨q, g, hqg, rfl⟩ := mem_ttRows.1 hr
  obtain ⟨hq, hg, i1, i2⟩ := hqg
  replace hq : q ∈ w.C := hq
  replace hg : g ∈ w.C := hg
  rw [Row.eval_tt]
  show xOf h q g + xOf h (nxt w.C q) g = 0
  -- the crease `q` lies in the closed interval of `g`, in the key order
  have k1 : w.pkey h (w.lc g) < w.pkey h q := by
    rw [← c_lc (w := w.perturb h) hg, perturb_lc (w := w) h hg] at i1
    exact (perturb_lt h (lc_mem hg) hq).1 i1
  have k2 : w.pkey h q < w.pkey h (w.uc g) := by
    rw [← c_uc (w := w.perturb h) hg, perturb_uc (w := w) h hg] at i2
    exact (perturb_lt h hq (uc_mem hg)).1 i2
  have c1 := c_le_of_pkey_lt h k1
  have c2 := c_le_of_pkey_lt h k2
  rw [c_lc (w := w) hg] at c1; rw [c_uc (w := w) hg] at c2
  by_cases e1 : w.c q = w.hi g
  · -- `q` on the ray of the upper end of `g`: a maximum with a smaller taco
    set u := w.uc g
    have hu : u ∈ w.C := uc_mem hg
    have hcu : w.c q = w.c u := e1.trans (c_uc hg).symm
    have hupu : w.up u := up_uc hg
    rcases Prod.Lex.toLex_lt_toLex.1 k2 with h1 | ⟨-, h1⟩
    · exact absurd h1 (by rw [hcu]; exact lt_irrefl _)
    simp only at h1
    rcases Prod.Lex.toLex_lt_toLex.1 h1 with h2 | ⟨h2, h3⟩
    · simp only [hupu, if_true] at h2; split_ifs at h2 <;> omega
    · have hupq : w.up q := by by_contra hc; simp [hc, hupu] at h2
      simp only at h3
      have hle : |h q - h (nxt w.C q)| ≤ |h u - h (nxt w.C u)| := by
        rcases Prod.Lex.toLex_lt_toLex.1 h3 with h4 | ⟨h4, -⟩ <;>
          simp only [hupq, hupu, if_true, one_mul] at h4 <;> [exact h4.le; exact h4.le]
      have hne : q ≠ u := fun e => by rw [e] at k2; exact lt_irrefl _ k2
      exact split_row hf ⟨hq, hu, hne, hcu, iff_of_true hupq hupu⟩ (mem_sectors_uc hg) hle
  by_cases e2 : w.c q = w.lo g
  · -- `q` on the ray of the lower end of `g`: a minimum with a smaller taco
    set u := w.lc g
    have hu : u ∈ w.C := lc_mem hg
    have hcu : w.c q = w.c u := e2.trans (c_lc hg).symm
    have hupu : ¬ w.up u := not_up_lc hg
    rcases Prod.Lex.toLex_lt_toLex.1 k1 with h1 | ⟨-, h1⟩
    · exact absurd h1 (by rw [hcu]; exact lt_irrefl _)
    simp only at h1
    rcases Prod.Lex.toLex_lt_toLex.1 h1 with h2 | ⟨h2, h3⟩
    · simp only [hupu, if_false] at h2; split_ifs at h2 <;> omega
    · have hupq : ¬ w.up q := by intro hc; simp [hc, hupu] at h2
      simp only at h3
      have hle : |h q - h (nxt w.C q)| ≤ |h u - h (nxt w.C u)| := by
        rcases Prod.Lex.toLex_lt_toLex.1 h3 with h4 | ⟨h4, -⟩ <;>
          simp only [hupq, hupu, if_false, neg_one_mul, neg_lt_neg_iff, neg_inj] at h4 <;>
          [exact h4.le; exact h4.ge]
      have hne : q ≠ u := fun e => by rw [e] at k1; exact lt_irrefl _ k1
      exact split_row hf ⟨hq, hu, hne, hcu, iff_of_false hupq hupu⟩ (mem_sectors_lc hg) hle
  · -- `q` strictly inside the interval of `g`: a row of the vertex
    have htt : w.IsTT q g := ⟨hq, hg, lt_of_le_of_ne c1 (Ne.symm e2), lt_of_le_of_ne c2 e1⟩
    have := hf.2 _ (tt_mem_rows htt)
    rwa [Row.eval_tt] at this

/-- **Corollary 3.**  (a) Every assignment of the layer variables satisfying the taco–tortilla
and taco–taco rows at a vertex has `M - V ≡ 2 (mod 4)`, and `M - V = ±2` if the vertex has
degree four or no taco–taco row.  (b) Every flat-folded state of a vertex has `M - V = ±2`
(Maekawa's theorem), proved from the linear rows; transitivity is used only through the
stacking order that fixes the perturbation. -/
theorem corollary3 :
    (∀ x : ι → ι → ZMod 2, w.Antisymm x → w.IsSol x →
      w.mv (w.asg x) % 4 = 2 ∧ (w.C.card = 4 ∨ w.NoTC → w.mv (w.asg x) = 2 ∨ w.mv (w.asg x) = -2)) ∧
    (∀ h : ι → ℤ, w.IsFlat h → w.mv (w.asg (xOf h)) = 2 ∨ w.mv (w.asg (xOf h)) = -2) := by
  refine ⟨fun x hx hs => ⟨mv_mod_four hx hs, fun hc => ?_⟩, fun h hf => ?_⟩
  · rcases hc with h4 | hn
    · have h1 := mv_mod_four hx hs
      rw [mv_eq] at h1 ⊢
      have := Finset.card_filter_le w.C (fun j => w.ext0 (w.asg x) j = 1)
      rw [h4] at h1 this ⊢
      set V := (w.C.filter fun j => w.ext0 (w.asg x) j = 1).card
      push_cast at h1 ⊢
      omega
    · exact (theorem2 hn).2.2.2 _ ⟨x, hx, hs, rfl⟩
  · have hm := maekawa_generic (w := w.perturb h) (generic_noTC (perturb_generic h))
      (antisymm_xOf (w := w.perturb h) hf.1) (prop2 hf)
    have e : (w.perturb h).asg (xOf h) = w.asg (xOf h) := by
      funext k
      simp only [asg, perturb_C]
      simp only [perturb_up (w := w) h k.2]
    rw [e] at hm
    exact hm

end Walk

end Origami
