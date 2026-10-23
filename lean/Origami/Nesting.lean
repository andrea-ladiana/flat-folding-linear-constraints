import Origami.Generic

/-!
# The pairs are nested

At a vertex without taco–taco rows, the pairs of Theorem 2, drawn as chords of the circle of
creases, do not cross: the creases strictly between the two creases of a pair, on either
side, are paired among themselves, like parentheses.

The proof crimps a sector of smallest angle (Lemma 6 of the paper, `lemma5`).  Its two
creases are paired, and they are consecutive, so their chord crosses no other; the other
pairs are those of the crimped walk, whose creases are those of the walk minus two, in the
same cyclic order.  Crossing of chords depends only on the cyclic order of the index type,
so the induction on the number of creases goes through.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The chords `{a, b}` and `{c, d}` of the circle cross: `c` and `d` lie on the two different
arcs cut by `a` and `b`. -/
def Cross (a b c d : ι) : Prop := (cbtw a c b ∧ cbtw b d a) ∨ (cbtw a d b ∧ cbtw b c a)

/-- A point strictly inside the arc from `a` to `b` is not inside the arc from `b` to `a`. -/
lemma cbtw_not_cbtw_swap {a b x : ι} (hab : a ≠ b) (h : cbtw a x b) : ¬ cbtw b x a := by
  intro h'
  cyc2

namespace Walk

variable {w : Walk ι α}

/-- The chord of two consecutive creases crosses no chord between creases of the walk. -/
lemma not_cross_nxt {p c d : ι} (hc : c ∈ w.C) (hd : d ∈ w.C) :
    ¬ Cross p (nxt w.C p) c d ∧ ¬ Cross (nxt w.C p) p c d := by
  have hsp := (nxt_spec w.nonempty p).2
  unfold Cross
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hsp c hc h
    · exact hsp d hd h
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact hsp d hd h
    · exact hsp c hc h

/-- The chord of two consecutive creases crosses no chord between two other creases. -/
lemma not_cross_cons {p a b : ι} (hp : p ∈ w.C) (ha : a ∈ w.C) (hb : b ∈ w.C) (hab : a ≠ b)
    (hap : a ≠ p) (han : a ≠ nxt w.C p) (hbp : b ≠ p) (hbn : b ≠ nxt w.C p) :
    ¬ Cross a b p (nxt w.C p) ∧ ¬ Cross a b (nxt w.C p) p := by
  have e1 := cbtw_nxt_iff (B := a) ha hp hb (Ne.symm hap) hbp
  have e2 := cbtw_nxt_iff (B := b) hb hp ha (Ne.symm hbp) hap
  have k1 : cbtw a p b → cbtw a (nxt w.C p) b := fun h =>
    (e1.1 h).resolve_right (Ne.symm hbn)
  have k2 : cbtw b p a → cbtw b (nxt w.C p) a := fun h =>
    (e2.1 h).resolve_right (Ne.symm han)
  unfold Cross
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact cbtw_not_cbtw_swap hab (k1 h) h'
    · exact cbtw_not_cbtw_swap hab h (k2 h')
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact cbtw_not_cbtw_swap hab h (k2 h')
    · exact cbtw_not_cbtw_swap hab (k1 h) h'

/-- **The pairs are nested.**  At a vertex without taco–taco rows, two pairs of creases of
Theorem 2 never cross as chords of the circle of creases. -/
theorem nested : ∀ (n : ℕ) (w : Walk ι α), w.C.card = n → w.NoTC →
    ∀ a ∈ w.C, ∀ b ∈ w.C, ∀ c ∈ w.C, ∀ d ∈ w.C, a ≠ b → c ≠ d →
      w.SameComp a b → w.SameComp c d → ¬ Cross a b c d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hcard hn a ha b hb c hc d hd hab hcd h1 h2 hx
  by_cases h2c : w.C.card = 2
  · -- with two creases, every crease is `a` or `b`
    have hC : ∀ x ∈ w.C, x = a ∨ x = b := by
      intro x hx'
      by_contra hne
      push_neg at hne
      have hsub : ({a, b, x} : Finset ι) ⊆ w.C := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm hne.1]),
        Finset.card_pair (Ne.symm hne.2)] at this
      omega
    have key : ∀ x ∈ w.C, ¬ cbtw a x b := by
      intro x hx'
      rcases hC x hx' with rfl | rfl
      · exact not_cbtw_left
      · exact not_cbtw_right
    rcases hx with ⟨h, -⟩ | ⟨h, -⟩
    · exact key c hc h
    · exact key d hd h
  have h4 : 4 ≤ w.C.card := by
    have := w.two_le; obtain ⟨m, hm⟩ := card_even (w := w); omega
  obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image w.C w.len w.nonempty
  have L := lemma5 hn ha₀ h4 hmin
  obtain ⟨⟨hpa, hcomp, -⟩, hC', hsame, -⟩ := L
  set R := runOfMin hn ha₀ h4 hmin
  set p := prv w.C a₀ with hp
  have hpC : p ∈ w.C := w.prv_mem ha₀
  have hnp : nxt w.C p = a₀ := nxt_prv ha₀
  -- a pair meeting `{p, a₀}` is `{p, a₀}`
  have hpair : ∀ x ∈ w.C, ∀ y ∈ w.C, x ≠ y → w.SameComp x y →
      (x = p ∨ x = a₀ ∨ y = p ∨ y = a₀) → (x = p ∧ y = a₀) ∨ (x = a₀ ∧ y = p) := by
    intro x hx' y hy' hxy hs hm
    have hp0 : ∀ z ∈ w.C, w.SameComp p z → z = p ∨ z = a₀ := hcomp
    rcases hm with rfl | rfl | rfl | rfl
    · rcases hp0 y hy' hs with e | e
      · exact absurd e.symm hxy
      · exact Or.inl ⟨rfl, e⟩
    · rcases hp0 y hy' (conn_trans hpa hs) with e | e
      · exact Or.inr ⟨rfl, e⟩
      · exact absurd e.symm hxy
    · rcases hp0 x hx' (conn_symm hs) with e | e
      · exact absurd e hxy
      · exact Or.inr ⟨e, rfl⟩
    · rcases hp0 x hx' (conn_trans hpa (conn_symm hs)) with e | e
      · exact Or.inl ⟨e, rfl⟩
      · exact absurd e hxy
  have hcons : ∀ {c d : ι}, c ∈ w.C → d ∈ w.C → ¬ Cross p a₀ c d ∧ ¬ Cross a₀ p c d := by
    intro c d hc hd
    have := not_cross_nxt (w := w) (p := p) hc hd
    rwa [hnp] at this
  by_cases hab' : a = p ∨ a = a₀ ∨ b = p ∨ b = a₀
  · rcases hpair a ha b hb hab h1 hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hcons hc hd).1 hx
    · exact (hcons hc hd).2 hx
  push_neg at hab'
  by_cases hcd' : c = p ∨ c = a₀ ∨ d = p ∨ d = a₀
  · have hk := not_cross_cons (w := w) hpC ha hb hab hab'.1 (hnp ▸ hab'.2.1) hab'.2.2.1
      (hnp ▸ hab'.2.2.2)
    rw [hnp] at hk
    rcases hpair c hc d hd hcd h2 hcd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hk.1 hx
    · exact hk.2 hx
  -- the four creases survive the crimp
  push_neg at hcd'
  have mem' : ∀ x ∈ w.C, x ≠ p → x ≠ a₀ → x ∈ (w.runCrimp R).C := by
    intro x hx' h1' h2'
    rw [hC']
    exact Finset.mem_erase.2 ⟨h2', Finset.mem_erase.2 ⟨h1', hx'⟩⟩
  have ha' := mem' a ha hab'.1 hab'.2.1
  have hb' := mem' b hb hab'.2.2.1 hab'.2.2.2
  have hc' := mem' c hc hcd'.1 hcd'.2.1
  have hd' := mem' d hd hcd'.2.2.1 hcd'.2.2.2
  have hcard' : (w.runCrimp R).C.card < n := by
    rw [hC', Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨(w.prv_ne ha₀).symm, ha₀⟩),
      Finset.card_erase_of_mem hpC]
    omega
  exact ih _ hcard' (w.runCrimp R) rfl (noTC_runCrimp hn R) a ha' b hb' c hc' d hd' hab hcd
    ((hsame a ha' b hb').1 h1) ((hsame c hc' d hd').1 h2) hx

end Walk

end Origami
