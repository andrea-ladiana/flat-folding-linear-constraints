import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Order

/-!
# Cyclic successor and predecessor inside a finite set

The creases of a vertex are the elements of a finite set `C` of a linearly ordered type,
read cyclically: `nxt C k` is the next element of `C` after `k` (wrapping around), and
`prv C k` the previous one.  Crimping a run of sectors deletes creases, i.e. replaces `C`
by a subset, and the successor of the smaller set is computed from that of `C`
(`nxt_erase`).  This is why the formalization indexes creases by subsets rather than
by `Fin n`: a sequence of crimps is a sequence of deletions.
-/

namespace Origami

variable {ι : Type*} [LinearOrder ι]

/-- `cbtw k i j`: going forward cyclically from `k`, the point `i` is met strictly
before `j`.  For `j = k` this means `i ≠ k` (a full turn). -/
def cbtw (k i j : ι) : Prop := if k < j then k < i ∧ i < j else (k < i ∨ i < j)

instance (k i j : ι) : Decidable (cbtw k i j) := by unfold cbtw; infer_instance

/-- Cyclic successor of `k` within `C`. -/
def nxt (C : Finset ι) (k : ι) : ι :=
  if h : (C.filter (k < ·)).Nonempty then (C.filter (k < ·)).min' h
  else if h' : C.Nonempty then C.min' h' else k

/-- Cyclic predecessor of `k` within `C`. -/
def prv (C : Finset ι) (k : ι) : ι :=
  if h : (C.filter (· < k)).Nonempty then (C.filter (· < k)).max' h
  else if h' : C.Nonempty then C.max' h' else k

section cbtw

lemma cbtw_self_right {k i : ι} : cbtw k i k ↔ i ≠ k := by
  unfold cbtw; simp only [lt_irrefl, ↓reduceIte]
  constructor
  · rintro (h | h) <;> order
  · intro h; rcases lt_or_gt_of_ne h with h | h
    · exact Or.inr h
    · exact Or.inl h

lemma not_cbtw_left {k j : ι} : ¬ cbtw k k j := by
  unfold cbtw; split_ifs <;> simp; order

lemma not_cbtw_right {k j : ι} : ¬ cbtw k j j := by
  unfold cbtw; split_ifs with h1
  · simp
  · rintro (h2 | h2)
    · exact h1 h2
    · exact lt_irrefl _ h2

/-- Two distinct points other than `k`: one of them comes first after `k`. -/
lemma cbtw_total {k j j' : ι} (hj : j ≠ k) (hj' : j' ≠ k) (h : j ≠ j') :
    cbtw k j j' ∨ cbtw k j' j := by
  unfold cbtw
  rcases lt_or_gt_of_ne hj with h1 | h1 <;> rcases lt_or_gt_of_ne hj' with h2 | h2 <;>
    rcases lt_or_gt_of_ne h with h3 | h3 <;>
    simp only [h1, h2, h3, true_and, and_true, true_or, or_true, if_true, if_false,
      not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le]


/-- Two distinct points other than `k`: one of them is met first when going backwards
from `k`. -/
lemma cbtw_total' {k j j' : ι} (hj : j ≠ k) (hj' : j' ≠ k) (h : j ≠ j') :
    cbtw j j' k ∨ cbtw j' j k := by
  unfold cbtw
  rcases lt_or_gt_of_ne hj with h1 | h1 <;> rcases lt_or_gt_of_ne hj' with h2 | h2 <;>
    rcases lt_or_gt_of_ne h with h3 | h3 <;>
    simp only [h1, h2, h3, true_and, and_true, true_or, or_true, if_true, if_false,
      not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr h3.le]

/-- closes goals built from `∧`, `∨` and order atoms -/
syntax "cb" : tactic
macro_rules
  | `(tactic| cb) => `(tactic| first | order | (left; cb) | (right; cb) | (constructor <;> cb))

/-- a decision procedure for statements about `cbtw` with few points -/
syntax "cyc" : tactic
macro_rules
  | `(tactic| cyc) => `(tactic| (unfold cbtw at *; split_ifs at * <;> casesm* _ ∧ _, _ ∨ _ <;> cb))

/-- If `p` lies on the arc from `k` to `j`, every other point of that arc lies before or
after `p`. -/
lemma cbtw_split {k p i j : ι} (hp : cbtw k p j) (hi : cbtw k i j) (hip : i ≠ p) :
    cbtw k i p ∨ cbtw p i j := by
  rcases lt_or_gt_of_ne hip with h | h <;> cyc

lemma cbtw_rotate {a b c : ι} (h : cbtw a b c) (hac : a ≠ c) : cbtw b c a := by
  cyc

end cbtw

section nxtprv

variable {C : Finset ι} {k : ι}

lemma nxt_spec (hC : C.Nonempty) (k : ι) :
    nxt C k ∈ C ∧ ∀ i ∈ C, ¬ cbtw k i (nxt C k) := by
  unfold nxt
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hm
    refine ⟨hm.1, fun i hi hb => ?_⟩
    unfold cbtw at hb
    rw [if_pos hm.2] at hb
    have := Finset.min'_le (C.filter (k < ·)) i (Finset.mem_filter.2 ⟨hi, hb.1⟩)
    exact absurd hb.2 (not_lt.2 this)
  · refine ⟨Finset.min'_mem _ hC, fun i hi hb => ?_⟩
    have hall : ∀ i ∈ C, i ≤ k := fun i hi => by
      by_contra hc
      exact h ⟨i, Finset.mem_filter.2 ⟨hi, lt_of_not_ge hc⟩⟩
    unfold cbtw at hb
    split_ifs at hb with h1
    · exact absurd (hall _ (Finset.min'_mem _ hC)) (not_le.2 h1)
    · rcases hb with hb | hb
      · exact absurd (hall i hi) (not_le.2 hb)
      · exact absurd (Finset.min'_le C i hi) (not_le.2 hb)

lemma nxt_mem (hC : C.Nonempty) (k : ι) : nxt C k ∈ C := (nxt_spec hC k).1

lemma prv_spec (hC : C.Nonempty) (k : ι) :
    prv C k ∈ C ∧ ∀ i ∈ C, ¬ cbtw (prv C k) i k := by
  unfold prv
  split_ifs with h
  · have hm := Finset.max'_mem _ h
    rw [Finset.mem_filter] at hm
    refine ⟨hm.1, fun i hi hb => ?_⟩
    unfold cbtw at hb
    rw [if_pos hm.2] at hb
    have := Finset.le_max' (C.filter (· < k)) i (Finset.mem_filter.2 ⟨hi, hb.2⟩)
    exact absurd hb.1 (not_lt.2 this)
  · refine ⟨Finset.max'_mem _ hC, fun i hi hb => ?_⟩
    have hall : ∀ i ∈ C, k ≤ i := fun i hi => by
      by_contra hc
      exact h ⟨i, Finset.mem_filter.2 ⟨hi, lt_of_not_ge hc⟩⟩
    unfold cbtw at hb
    split_ifs at hb with h1
    · exact absurd (hall _ (Finset.max'_mem _ hC)) (not_le.2 h1)
    · rcases hb with hb | hb
      · exact absurd (Finset.le_max' C i hi) (not_le.2 hb)
      · exact absurd (hall i hi) (not_le.2 hb)

lemma prv_mem (hC : C.Nonempty) (k : ι) : prv C k ∈ C := (prv_spec hC k).1

/-- The successor is the unique element of `C` with nothing of `C` in between. -/
lemma eq_nxt_iff (hC : C.Nonempty) {j : ι} :
    j = nxt C k ↔ j ∈ C ∧ ∀ i ∈ C, ¬ cbtw k i j := by
  refine ⟨fun h => h ▸ nxt_spec hC k, fun ⟨hj, hb⟩ => ?_⟩
  obtain ⟨hn, hbn⟩ := nxt_spec hC k
  by_contra hne
  by_cases hjk : j = k
  · subst hjk
    exact hb _ hn (cbtw_self_right.2 (fun h => hne h.symm))
  by_cases hnk : nxt C k = k
  · rw [hnk] at hbn
    exact hbn _ hj (cbtw_self_right.2 hjk)
  rcases cbtw_total hjk hnk hne with h | h
  · exact hbn _ hj h
  · exact hb _ hn h

lemma eq_prv_iff (hC : C.Nonempty) {j : ι} :
    j = prv C k ↔ j ∈ C ∧ ∀ i ∈ C, ¬ cbtw j i k := by
  refine ⟨fun h => h ▸ prv_spec hC k, fun ⟨hj, hb⟩ => ?_⟩
  obtain ⟨hn, hbn⟩ := prv_spec hC k
  by_contra hne
  by_cases hjk : j = k
  · subst hjk
    exact hb _ hn (cbtw_self_right.2 (fun h => hne h.symm))
  by_cases hnk : prv C k = k
  · rw [hnk] at hbn
    exact hbn _ hj (cbtw_self_right.2 hjk)
  rcases cbtw_total' hjk hnk hne with h | h
  · exact hb _ hn h
  · exact hbn _ hj h

lemma nxt_prv (hk : k ∈ C) : nxt C (prv C k) = k := by
  have hC : C.Nonempty := ⟨k, hk⟩
  exact ((eq_nxt_iff hC).2 ⟨hk, (prv_spec hC k).2⟩).symm

lemma prv_nxt (hk : k ∈ C) : prv C (nxt C k) = k := by
  have hC : C.Nonempty := ⟨k, hk⟩
  exact ((eq_prv_iff hC).2 ⟨hk, (nxt_spec hC k).2⟩).symm

lemma nxt_injOn : Set.InjOn (nxt C) C := fun a ha b hb h => by
  rw [← prv_nxt ha, ← prv_nxt hb, h]

lemma prv_injOn : Set.InjOn (prv C) C := fun a ha b hb h => by
  rw [← nxt_prv ha, ← nxt_prv hb, h]

lemma nxt_ne (hk : k ∈ C) (h2 : 2 ≤ C.card) : nxt C k ≠ k := by
  intro h
  have hC : C.Nonempty := ⟨k, hk⟩
  have hb := (nxt_spec hC k).2
  rw [h] at hb
  have : C ⊆ {k} := fun i hi => by
    by_contra hik
    exact hb i hi (cbtw_self_right.2 (by simpa using hik))
  have := Finset.card_le_card this
  simp at this; omega

lemma prv_ne (hk : k ∈ C) (h2 : 2 ≤ C.card) : prv C k ≠ k := by
  intro h
  have hC : C.Nonempty := ⟨k, hk⟩
  have := nxt_ne (prv_mem hC k) h2
  rw [nxt_prv hk, h] at this
  exact this rfl

/-- Deleting an element `p ≠ k` from `C`. -/
lemma nxt_erase {p : ι} (hk : k ∈ C) (hp : p ∈ C) (hkp : k ≠ p) :
    nxt (C.erase p) k = if nxt C k = p then nxt C p else nxt C k := by
  have hC : C.Nonempty := ⟨k, hk⟩
  have hC' : (C.erase p).Nonempty := ⟨k, Finset.mem_erase.2 ⟨hkp, hk⟩⟩
  symm
  rw [eq_nxt_iff hC']
  split_ifs with h
  · refine ⟨Finset.mem_erase.2 ⟨fun hpp => ?_, nxt_mem hC p⟩, fun i hi hb => ?_⟩
    · -- `nxt p = p` forces `C = {p}`
      have := nxt_ne hp (by
        have : ({k, p} : Finset ι) ⊆ C := by
          intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
        have := Finset.card_le_card this
        rwa [Finset.card_pair hkp] at this)
      exact this hpp
    · obtain ⟨hip, hiC⟩ := Finset.mem_erase.1 hi
      have hk1 := (nxt_spec hC k).2 i hiC
      have hp1 := (nxt_spec hC p).2 i hiC
      rw [h] at hk1
      -- `i` lies strictly between `k` and `nxt p`; then it lies before or after `p`
      by_cases hik : i = k
      · subst hik; exact not_cbtw_left hb
      by_cases hnk : nxt C p = k
      · rw [hnk] at hb hp1
        rcases cbtw_total' (j := p) (j' := i) (k := k) (Ne.symm hkp) hik (Ne.symm hip)
          with h1 | h1
        · exact hp1 h1
        · exact hk1 (cbtw_rotate (cbtw_rotate h1 hik) (Ne.symm hip))
      · -- `p` lies on the arc from `k` to `nxt p`
        have hpk : nxt C p ≠ p := fun hpp => hnk (by
          exfalso
          have := nxt_ne hp (by
            have : ({k, p} : Finset ι) ⊆ C := by
              intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
            have := Finset.card_le_card this
            rwa [Finset.card_pair hkp] at this)
          exact this hpp)
        have hkpj : cbtw k p (nxt C p) := by
          rcases cbtw_total (k := k) (Ne.symm hkp) hnk (Ne.symm hpk) with h1 | h1
          · exact h1
          · have := (nxt_spec hC k).2 _ (nxt_mem hC p)
            rw [h] at this
            exact absurd h1 this
        rcases cbtw_split hkpj hb hip with h1 | h1
        · exact hk1 h1
        · exact hp1 h1
  · exact ⟨Finset.mem_erase.2 ⟨h, nxt_mem hC k⟩,
      fun i hi => (nxt_spec hC k).2 i (Finset.mem_of_mem_erase hi)⟩

lemma two_le_of_ne {p : ι} (hk : k ∈ C) (hp : p ∈ C) (hkp : k ≠ p) : 2 ≤ C.card := by
  have : ({k, p} : Finset ι) ⊆ C := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have := Finset.card_le_card this
  rwa [Finset.card_pair hkp] at this

lemma prv_erase {p : ι} (hk : k ∈ C) (hp : p ∈ C) (hkp : k ≠ p) :
    prv (C.erase p) k = if prv C k = p then prv C p else prv C k := by
  have hC : C.Nonempty := ⟨k, hk⟩
  have h2 := two_le_of_ne hk hp hkp
  set j := if prv C k = p then prv C p else prv C k with hj
  have hjC : j ∈ C.erase p := by
    rw [hj]; split_ifs with h
    · exact Finset.mem_erase.2 ⟨prv_ne hp h2, prv_mem hC p⟩
    · exact Finset.mem_erase.2 ⟨h, prv_mem hC k⟩
  have hnj : nxt (C.erase p) j = k := by
    rw [nxt_erase (Finset.mem_of_mem_erase hjC) hp (Finset.ne_of_mem_erase hjC), hj]
    split_ifs with h1 h2' h2'
    · rw [← h1, nxt_prv hk]
    · rw [nxt_prv hp] at h2'; exact absurd rfl h2'
    · rw [nxt_prv hk] at h2'; exact absurd h2' hkp
    · rw [nxt_prv hk]
  rw [← hnj, prv_nxt hjC]

/-- If going forward twice returns to `k`, the set has at most two elements. -/
lemma card_le_two_of_nxt_nxt (hk : k ∈ C) (h : nxt C (nxt C k) = k) : C.card ≤ 2 := by
  have hC : C.Nonempty := ⟨k, hk⟩
  by_cases h1 : C.card ≤ 1
  · omega
  have h2 : 2 ≤ C.card := by omega
  have hsub : C ⊆ {k, nxt C k} := by
    intro i hi
    by_contra hi'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
    have hb1 := (nxt_spec hC k).2 i hi
    have hb2 := (nxt_spec hC (nxt C k)).2 i hi
    rw [h] at hb2
    rcases cbtw_total (k := k) hi'.1 (nxt_ne hk h2) hi'.2 with h3 | h3
    · exact hb1 h3
    · exact hb2 (cbtw_rotate h3 (Ne.symm hi'.1))
  have := Finset.card_le_card hsub
  have := Finset.card_insert_le k ({nxt C k} : Finset ι)
  simp at *; omega

lemma nxt_ne_prv (hk : k ∈ C) (h3 : 3 ≤ C.card) : nxt C k ≠ prv C k := by
  intro h
  have hC : C.Nonempty := ⟨k, hk⟩
  have : nxt C (nxt C (prv C k)) = prv C k := by rw [nxt_prv hk, h]
  have := card_le_two_of_nxt_nxt (prv_mem hC k) this
  omega

/-- Deleting two consecutive elements `p, nxt p` from `C`. -/
lemma nxt_erase_pair {p : ι} (hp : p ∈ C) (h4 : 4 ≤ C.card) (hk : k ∈ (C.erase p).erase (nxt C p)) :
    nxt ((C.erase p).erase (nxt C p)) k = if k = prv C p then nxt C (nxt C p) else nxt C k := by
  have hC : C.Nonempty := ⟨p, hp⟩
  have h2 : 2 ≤ C.card := by omega
  obtain ⟨hk1, hk2⟩ := Finset.mem_erase.1 hk
  obtain ⟨hk3, hkC⟩ := Finset.mem_erase.1 hk2
  have hq : nxt C p ∈ C.erase p := Finset.mem_erase.2 ⟨nxt_ne hp h2, nxt_mem hC p⟩
  rw [nxt_erase hk2 hq hk1, nxt_erase hkC hp hk3, nxt_erase (nxt_mem hC p) hp (nxt_ne hp h2)]
  have hnn : nxt C (nxt C p) ≠ p := by
    intro h
    -- then `C = {p, nxt p}`, contradicting `4 ≤ card`
    have hsub : C ⊆ {p, nxt C p} := by
      intro i hi
      by_contra hi'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
      have hb1 := (nxt_spec hC p).2 i hi
      have hb2 := (nxt_spec hC (nxt C p)).2 i hi
      rw [h] at hb2
      rcases cbtw_total (k := p) hi'.1 (nxt_ne hp h2) hi'.2 with h3 | h3
      · exact hb1 h3
      · exact hb2 (cbtw_rotate h3 (Ne.symm hi'.1))
    have := Finset.card_le_card hsub
    have := Finset.card_insert_le p ({nxt C p} : Finset ι)
    simp at *; omega
  by_cases hkp : k = prv C p
  · subst hkp
    simp [nxt_prv hp, hnn]
  · have : nxt C k ≠ p := fun h => hkp (by rw [← h, prv_nxt hkC])
    simp only [this, if_false, hkp]
    have : nxt C k ≠ nxt C p := fun h => hk3 (nxt_injOn hkC hp h)
    simp [this]

lemma prv_erase_pair {p : ι} (hp : p ∈ C) (h4 : 4 ≤ C.card) (hk : k ∈ (C.erase p).erase (nxt C p)) :
    prv ((C.erase p).erase (nxt C p)) k = if k = nxt C (nxt C p) then prv C p else prv C k := by
  have hC : C.Nonempty := ⟨p, hp⟩
  have h2 : 2 ≤ C.card := by omega
  obtain ⟨hk1, hk2⟩ := Finset.mem_erase.1 hk
  obtain ⟨hk3, hkC⟩ := Finset.mem_erase.1 hk2
  have hq : nxt C p ∈ C.erase p := Finset.mem_erase.2 ⟨nxt_ne hp h2, nxt_mem hC p⟩
  rw [prv_erase hk2 hq hk1, prv_erase hkC hp hk3]
  have hpq : prv C (nxt C p) = p := prv_nxt hp
  by_cases hkq : k = nxt C (nxt C p)
  · subst hkq
    rw [prv_nxt (nxt_mem hC p)]
    simp only [if_true]
    rw [prv_erase (nxt_mem hC p) hp (nxt_ne hp h2), hpq]
    simp [nxt_ne hp h2]
  · have h1 : prv C k ≠ nxt C p := fun h => hkq (by rw [← h, nxt_prv hkC])
    have h1' : prv C k ≠ p := fun h => hk1 (by rw [← h, nxt_prv hkC])
    simp [h1, h1', hkq]

/-- Induction around the cycle: a property of one element of `C` that passes from every
element to its successor holds on all of `C`. -/
lemma cycle_induction (P : ι → Prop) {k₀ : ι} (hk₀ : k₀ ∈ C) (h₀ : P k₀)
    (hstep : ∀ k ∈ C, P k → P (nxt C k)) : ∀ k ∈ C, P k := by
  classical
  have hC : C.Nonempty := ⟨k₀, hk₀⟩
  set m := C.min' hC with hm
  -- below `k` in `C` there are fewer elements than below `nxt k`, unless `k` is the maximum
  have hprv_lt : ∀ k ∈ C, k ≠ m → prv C k < k := by
    intro k hk hkm
    have hne : (C.filter (· < k)).Nonempty :=
      ⟨m, Finset.mem_filter.2 ⟨Finset.min'_mem _ _, lt_of_le_of_ne (Finset.min'_le _ _ hk)
        (Ne.symm hkm)⟩⟩
    unfold prv; rw [dif_pos hne]
    exact (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
  -- the set of good elements is closed under `prv`
  have hS : ∀ k ∈ C, P k → P (prv C k) := by
    intro k hk hPk
    -- `nxt` restricted to the good set is injective, hence surjective onto it
    set S := C.filter P
    have hmaps : ∀ x ∈ S, nxt C x ∈ S := fun x hx => by
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨nxt_mem hC x, hstep x hx.1 hx.2⟩
    have hinj : ∀ a ∈ S, ∀ b ∈ S, nxt C a = nxt C b → a = b := fun a ha b hb h =>
      nxt_injOn (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) h
    have hsurj := Finset.surjOn_of_injOn_of_card_le (s := S) (t := S) (nxt C)
      (fun x hx => hmaps x hx) (fun a ha b hb h => hinj a ha b hb h) le_rfl
    obtain ⟨x, hx, hxk⟩ := hsurj (Finset.mem_filter.2 ⟨hk, hPk⟩)
    have : x = prv C k := by rw [← hxk, prv_nxt (Finset.mem_of_mem_filter x hx)]
    rw [← this]; exact (Finset.mem_filter.1 hx).2
  -- going down from `k₀`, the minimum is good
  have hmin : P m := by
    suffices ∀ n : ℕ, ∀ k ∈ C, (C.filter (· < k)).card = n → P k → P m from
      this _ k₀ hk₀ rfl h₀
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk hn hPk
      by_cases hkm : k = m
      · rw [← hkm]; exact hPk
      · have hlt := hprv_lt k hk hkm
        refine ih _ ?_ (prv C k) (prv_mem hC k) rfl (hS k hk hPk)
        rw [← hn]
        apply Finset.card_lt_card
        refine ⟨fun x hx => ?_, fun h => ?_⟩
        · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hlt⟩
        · have := h (Finset.mem_filter.2 ⟨prv_mem hC k, hlt⟩)
          simp at this
  -- going up from the minimum, every element is good
  intro k hk
  suffices ∀ n : ℕ, ∀ k ∈ C, (C.filter (· < k)).card = n → P k from this _ k hk rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk hn
    by_cases hkm : k = m
    · rw [hkm]; exact hmin
    · have hlt := hprv_lt k hk hkm
      have := ih _ ?_ (prv C k) (prv_mem hC k) rfl
      · rw [← nxt_prv hk]; exact hstep _ (prv_mem hC k) this
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun h => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hlt⟩
      · have := h (Finset.mem_filter.2 ⟨prv_mem hC k, hlt⟩)
        simp at this

/-- If `j ≥ 1` steps forward return to `k`, the set has at most `j` elements. -/
lemma card_le_of_iterate (hk : k ∈ C) {j : ℕ} (hj : 0 < j) (h : (nxt C)^[j] k = k) :
    C.card ≤ j := by
  classical
  have hC : C.Nonempty := ⟨k, hk⟩
  have hsub : C ⊆ (Finset.range j).image fun t => (nxt C)^[t] k := by
    intro i hi
    refine cycle_induction (fun i => i ∈ (Finset.range j).image fun t => (nxt C)^[t] k) hk
      (Finset.mem_image.2 ⟨0, Finset.mem_range.2 hj, rfl⟩) ?_ i hi
    intro i _ hi'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hi'
    rw [Finset.mem_range] at ht
    by_cases ht' : t + 1 < j
    · exact Finset.mem_image.2 ⟨t + 1, Finset.mem_range.2 ht',
        by rw [Function.iterate_succ_apply']⟩
    · have : t + 1 = j := by omega
      refine Finset.mem_image.2 ⟨0, Finset.mem_range.2 hj, ?_⟩
      rw [Function.iterate_zero_apply, ← Function.iterate_succ_apply' (nxt C),
        Nat.succ_eq_add_one, this, h]
  calc C.card ≤ ((Finset.range j).image fun t => (nxt C)^[t] k).card := Finset.card_le_card hsub
    _ ≤ (Finset.range j).card := Finset.card_image_le
    _ = j := Finset.card_range j

lemma iterate_mem (hk : k ∈ C) (i : ℕ) : (nxt C)^[i] k ∈ C := by
  induction i with
  | zero => exact hk
  | succ i ih => rw [Function.iterate_succ_apply']; exact nxt_mem ⟨k, hk⟩ _

/-- The first `card C` iterates of `nxt` are distinct. -/
lemma iterate_inj (hk : k ∈ C) {i j : ℕ} (hi : i < C.card) (hj : j < C.card)
    (h : (nxt C)^[i] k = (nxt C)^[j] k) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hij
  · have e : (nxt C)^[j - i] ((nxt C)^[i] k) = (nxt C)^[i] k := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, h]
    have := card_le_of_iterate (iterate_mem hk i) (by omega) e
    omega
  · have e : (nxt C)^[i - j] ((nxt C)^[j] k) = (nxt C)^[j] k := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, h]
    have := card_le_of_iterate (iterate_mem hk j) (by omega) e
    omega

lemma prv_iterate_succ (hk : k ∈ C) (i : ℕ) : prv C ((nxt C)^[i + 1] k) = (nxt C)^[i] k := by
  rw [Function.iterate_succ_apply', prv_nxt (iterate_mem hk i)]

/-- Going once around the cycle. -/
lemma iterate_card (hk : k ∈ C) : (nxt C)^[C.card] k = k := by
  classical
  have hC : C.Nonempty := ⟨k, hk⟩
  have hn : 0 < C.card := Finset.card_pos.2 hC
  -- the first `card C` iterates are distinct, so they exhaust `C`
  have himg : (Finset.range C.card).image (fun i => (nxt C)^[i] k) = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact iterate_mem hk i
    · rw [Finset.card_image_of_injOn (fun i hi j hj e => iterate_inj hk
        (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) e), Finset.card_range]
  have hm : (nxt C)^[C.card] k ∈ (Finset.range C.card).image (fun i => (nxt C)^[i] k) := by
    rw [himg]; exact iterate_mem hk _
  obtain ⟨j, hj, e⟩ := Finset.mem_image.1 hm
  rw [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0] at e; exact e.symm
  · exfalso
    have e' : (nxt C)^[j - 1 + 1] k = (nxt C)^[C.card - 1 + 1] k := by
      rw [Nat.sub_add_cancel hpos, Nat.sub_add_cancel hn, e]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at e'
    have := iterate_inj hk (i := j - 1) (j := C.card - 1) (by omega) (by omega)
      (nxt_injOn (iterate_mem hk _) (iterate_mem hk _) e')
    omega

/-- Every element is reached from `k` within one turn. -/
lemma exists_iterate (hk : k ∈ C) {g : ι} (hg : g ∈ C) : ∃ i < C.card, g = (nxt C)^[i] k := by
  classical
  have himg : (Finset.range C.card).image (fun i => (nxt C)^[i] k) = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact iterate_mem hk i
    · rw [Finset.card_image_of_injOn (fun i hi j hj e => iterate_inj hk
        (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) e), Finset.card_range]
  have : g ∈ (Finset.range C.card).image (fun i => (nxt C)^[i] k) := by rw [himg]; exact hg
  obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
  exact ⟨i, Finset.mem_range.1 hi, e.symm⟩

lemma prv_eq_iterate (hk : k ∈ C) : prv C k = (nxt C)^[C.card - 1] k := by
  have hC : C.Nonempty := ⟨k, hk⟩
  have hn : 0 < C.card := Finset.card_pos.2 hC
  have := prv_iterate_succ hk (C.card - 1)
  rwa [Nat.sub_add_cancel hn, iterate_card hk] at this

/-- The elements of `C` strictly between `k` and its `(d+1)`-th successor are its
`j`-th successors, `1 ≤ j ≤ d`. -/
lemma between_iterate (hk : k ∈ C) : ∀ d : ℕ, d + 1 < C.card → ∀ i ∈ C,
    cbtw k i ((nxt C)^[d + 1] k) → ∃ j, 1 ≤ j ∧ j ≤ d ∧ i = (nxt C)^[j] k := by
  have hC : C.Nonempty := ⟨k, hk⟩
  intro d
  induction d with
  | zero =>
    intro _ i hi hb
    exact absurd hb ((nxt_spec hC k).2 i hi)
  | succ d ih =>
    intro hd i hi hb
    set p := (nxt C)^[d + 1] k with hp
    set q := (nxt C)^[d + 2] k with hq
    have hqp : q = nxt C p := by rw [hq, hp, Function.iterate_succ_apply']
    have hpk : p ≠ k := fun e => by
      have := iterate_inj hk (i := d + 1) (j := 0) (by omega) (by omega) (by rw [← hp, e]; rfl)
      omega
    have hqk : q ≠ k := fun e => by
      have := iterate_inj hk (i := d + 2) (j := 0) (by omega) (by omega) (by rw [← hq, e]; rfl)
      omega
    have hpq : p ≠ q := fun e => by
      have := iterate_inj hk (i := d + 1) (j := d + 2) (by omega) (by omega) (by rw [← hp, ← hq, e])
      omega
    -- `p` lies on the arc from `k` to `q`
    have hkpq : cbtw k p q := by
      rcases cbtw_total hpk hqk hpq with h | h
      · exact h
      · exfalso
        obtain ⟨j, hj1, hjd, hjq⟩ := ih (by omega) q (iterate_mem hk _) h
        have := iterate_inj hk (i := d + 2) (j := j) (by omega) (by omega) (by rw [← hq, hjq])
        omega
    by_cases hip : i = p
    · exact ⟨d + 1, by omega, le_rfl, hip⟩
    rcases cbtw_split hkpq hb hip with h | h
    · obtain ⟨j, hj1, hjd, hji⟩ := ih (by omega) i hi h
      exact ⟨j, hj1, by omega, hji⟩
    · rw [hqp] at h
      exact absurd h ((nxt_spec hC p).2 i hi)

/-- Successor after deleting a set `B`: the first element after `k` that survives. -/
lemma nxt_sdiff {B : Finset ι} {j : ι} (hk : k ∈ C) (hkB : k ∉ B) (hj : j ∈ C) (hjB : j ∉ B)
    (hbtw : ∀ i ∈ C, cbtw k i j → i ∈ B) : nxt (C \ B) k = j := by
  have hne : (C \ B).Nonempty := ⟨k, Finset.mem_sdiff.2 ⟨hk, hkB⟩⟩
  symm; rw [eq_nxt_iff hne]
  refine ⟨Finset.mem_sdiff.2 ⟨hj, hjB⟩, fun i hi hb => ?_⟩
  exact (Finset.mem_sdiff.1 hi).2 (hbtw i (Finset.mem_sdiff.1 hi).1 hb)

lemma prv_sdiff {B : Finset ι} {j : ι} (hk : k ∈ C) (hkB : k ∉ B) (hj : j ∈ C) (hjB : j ∉ B)
    (hbtw : ∀ i ∈ C, cbtw k i j → i ∈ B) : prv (C \ B) j = k := by
  rw [← nxt_sdiff hk hkB hj hjB hbtw, prv_nxt (Finset.mem_sdiff.2 ⟨hk, hkB⟩)]

/-- If the successor survives, it is still the successor. -/
lemma nxt_sdiff_of_mem {B : Finset ι} (hk : k ∈ C) (hkB : k ∉ B) (hnB : nxt C k ∉ B) :
    nxt (C \ B) k = nxt C k :=
  nxt_sdiff hk hkB (nxt_mem ⟨k, hk⟩ k) hnB fun i hi hb =>
    absurd hb ((nxt_spec ⟨k, hk⟩ k).2 i hi)

lemma prv_sdiff_of_mem {B : Finset ι} (hk : k ∈ C) (hkB : k ∉ B) (hpB : prv C k ∉ B) :
    prv (C \ B) k = prv C k := by
  have hC : C.Nonempty := ⟨k, hk⟩
  have := nxt_sdiff_of_mem (B := B) (prv_mem hC k) hpB (by rw [nxt_prv hk]; exact hkB)
  rw [nxt_prv hk] at this
  calc prv (C \ B) k = prv (C \ B) (nxt (C \ B) (prv C k)) := by rw [this]
    _ = prv C k := prv_nxt (Finset.mem_sdiff.2 ⟨prv_mem hC k, hpB⟩)

end nxtprv

end Origami
