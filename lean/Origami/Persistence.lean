import Origami.Nesting

/-!
# The pairs are the persistence pairs of the heights

At a vertex without taco–taco rows, read the positions `c k` of the creases as a height
function on the circle of the paper around the vertex, and sweep a level upwards.  A
minimum `e_m` is born at the level `c m`.  Its sublevel arc grows until, at a maximum
`e_M`, it merges with an arc that contains a lower minimum (the elder rule).  The pair
`{e_m, e_M}` is a persistence pair.  The highest and the lowest crease form the essential
pair.  This file proves that the pairs of Theorem 2 are exactly these pairs (Theorem 3 of
the paper).

The elder rule is written in terms of the cyclic order only (`PersPair`): from `e_m` one
direction reaches `e_M` with the heights in between above `c m`; continuing past `e_M`, it
reaches a crease `e_y` below `c m` without rising above `c M`; the other direction from `e_m`
reaches a crease `e_z` above `c M` before falling below `c m`.

The proof crimps a sector of smallest angle (Lemma 6 of the paper, `lemma5`).  Its two creases
form a persistence pair, and the persistence pairs of the other creases are those of the crimped
walk.  The converse uses that a minimum has only one persistence partner.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-! ### Cyclic order -/

lemma cbtw_trans_left {k a b d : ι} (h1 : cbtw k a b) (h2 : cbtw k b d) : cbtw k a d := by
  cyc2

lemma cbtw_trans_right {a b d x : ι} (h1 : cbtw a b d) (h2 : cbtw b x d) : cbtw a x d := by
  cyc2

namespace Walk

variable (w : Walk ι α)

/-! ### The elder rule -/

/-- The essential pair: `e_a` is a highest crease and `e_b` a lowest one. -/
def Essential (a b : ι) : Prop :=
  a ∈ w.C ∧ b ∈ w.C ∧ (∀ k ∈ w.C, w.c k ≤ w.c a) ∧ ∀ k ∈ w.C, w.c b ≤ w.c k

/-- The elder rule, read forward from `e_m`: the heights stay above `c m` up to `e_M`, and
below `c M` up to `e_y`; behind `e_m` they stay above `c m` back to `e_z`. -/
def PersR (m M y z : ι) : Prop :=
  cbtw m M y ∧ (∀ x ∈ w.C, cbtw m x M → w.c m < w.c x) ∧
    (∀ x ∈ w.C, cbtw m x y → w.c x ≤ w.c M) ∧ ∀ x ∈ w.C, cbtw z x m → w.c m < w.c x

/-- The elder rule, read backward from `e_m`. -/
def PersL (m M y z : ι) : Prop :=
  cbtw y M m ∧ (∀ x ∈ w.C, cbtw M x m → w.c m < w.c x) ∧
    (∀ x ∈ w.C, cbtw y x m → w.c x ≤ w.c M) ∧ ∀ x ∈ w.C, cbtw m x z → w.c m < w.c x

/-- **Persistence pair** (elder rule).  The minimum `e_m` dies at the maximum `e_M`.  In one
direction from `e_m` the walk reaches `e_M` staying above `c m`, then a crease `e_y` below
`c m` without rising above `c M`: at the level `c M` the sublevel arc of `e_m` merges with
the arc of a lower minimum.  In the other direction it reaches a crease `e_z` above `c M`
before falling below `c m`, so no merge happens earlier on that side. -/
def PersPair (m M : ι) : Prop :=
  m ∈ w.C ∧ M ∈ w.C ∧ w.c m < w.c M ∧ ∃ y ∈ w.C, w.c y < w.c m ∧ ∃ z ∈ w.C, w.c M < w.c z ∧
    (w.PersR m M y z ∨ w.PersL m M y z)

variable {w}

/-! ### Creases next to each other -/

/-- After `k`, its successor comes before every other crease. -/
lemma cbtw_nxt_left {k g : ι} (hg : g ∈ w.C) (hgn : g ≠ nxt w.C k) : cbtw k (nxt w.C k) g :=
  (cbtw_or_cbtw (k := k) hgn).resolve_left ((nxt_spec w.nonempty k).2 g hg)

/-- Before `k`, its predecessor comes after every other crease. -/
lemma cbtw_prv_right {k g : ι} (hk : k ∈ w.C) (hg : g ∈ w.C) (hgp : g ≠ prv w.C k) :
    cbtw g (prv w.C k) k :=
  cbtw_of_not_cbtw (Ne.symm hgp) (w.prv_ne hk) ((prv_spec w.nonempty k).2 g hg)

/-- The only crease between the neighbours of `k` is `k`. -/
lemma eq_of_cbtw_prv_nxt {k x : ι} (hk : k ∈ w.C) (hx : x ∈ w.C)
    (h : cbtw (prv w.C k) x (nxt w.C k)) : x = k := by
  by_contra hxk
  have h0 : cbtw (prv w.C k) k (nxt w.C k) := cbtw_nxt (w.prv_mem hk) hk (w.prv_ne hk).symm
  have h1 : ¬ cbtw (prv w.C k) x k := (prv_spec w.nonempty k).2 x hx
  have h2 : ¬ cbtw k x (nxt w.C k) := (nxt_spec w.nonempty k).2 x hx
  cyc2

/-- A crease met between two others, before or after the consecutive creases `p, nxt p`:
the outer neighbours `prv p` and `nxt (nxt p)` lie on the same closed arc. -/
lemma crimp_between {p a b : ι} (hp : p ∈ w.C) (ha : a ∈ w.C) (hb : b ∈ w.C) (hap : a ≠ p)
    (haq : a ≠ nxt w.C p) (hbp : b ≠ p) (hbq : b ≠ nxt w.C p)
    (h : cbtw a p b ∨ cbtw a (nxt w.C p) b) :
    (prv w.C p = a ∨ cbtw a (prv w.C p) b) ∧
      (nxt w.C (nxt w.C p) = b ∨ cbtw a (nxt w.C (nxt w.C p)) b) := by
  have hq := w.nxt_mem hp
  have e1 := cbtw_nxt_iff (B := a) ha hp hb (Ne.symm hap) hbp
  have hpq : cbtw a p b ∧ cbtw a (nxt w.C p) b := by
    rcases h with h | h
    · exact ⟨h, (e1.1 h).resolve_right (Ne.symm hbq)⟩
    · exact ⟨e1.2 (Or.inl h), h⟩
  refine ⟨?_, ?_⟩
  · by_cases hua : prv w.C p = a
    · exact Or.inl hua
    right
    have hPa : cbtw a (prv w.C p) p := by
      have := cbtw_nxt (w := w) ha (w.prv_mem hp) hua
      rwa [nxt_prv hp] at this
    by_cases hub : b = prv w.C p
    · rw [hub] at hpq
      exact absurd hpq.1 (cbtw_asymm hPa)
    have e2 := cbtw_nxt_iff (B := a) ha (w.prv_mem hp) hb hua hub
    rw [nxt_prv hp] at e2
    exact e2.2 (Or.inl hpq.1)
  · rcases (cbtw_nxt_iff (B := a) ha hq hb (Ne.symm haq) hbq).1 hpq.2 with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

/-! ### A persistence pair joins a minimum to a maximum, and is determined by its minimum -/

lemma persPair_up {m M : ι} (h : w.PersPair m M) : ¬ w.up m ∧ w.up M := by
  obtain ⟨hm, hM, hmM, y, -, -, z, -, -, ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩⟩ := h
  · refine ⟨?_, ?_⟩
    · rw [not_up_iff_nxt hm]
      by_cases e : nxt w.C m = M
      · rw [e]; exact hmM
      · exact h2 _ (w.nxt_mem hm) (cbtw_nxt_left hM (Ne.symm e))
    · show w.c (prv w.C M) < w.c M
      by_cases e : prv w.C M = m
      · rw [e]; exact hmM
      · have hb := cbtw_prv_right hM hm (Ne.symm e)
        exact lt_of_le_of_ne (h3 _ (w.prv_mem hM) (cbtw_trans_left hb h1)) (c_prv_ne hM)
  · refine ⟨?_, ?_⟩
    · rw [not_up_iff hm]
      by_cases e : prv w.C m = M
      · rw [e]; exact hmM
      · exact h2 _ (w.prv_mem hm) (cbtw_prv_right hm hM (Ne.symm e))
    · rw [up_iff_nxt hM]
      by_cases e : nxt w.C M = m
      · rw [e]; exact hmM
      · have hb := cbtw_nxt_left (k := M) hm (Ne.symm e)
        exact lt_of_le_of_ne (h3 _ (w.nxt_mem hM) (cbtw_trans_right h1 hb)) (c_nxt_ne hM)

lemma le_of_persR {m M M' y z y' z' : ι} (hM : M ∈ w.C) (hy' : y' ∈ w.C)
    (hym' : w.c y' < w.c m) (hmM : w.c m < w.c M) (h : w.PersR m M y z)
    (h' : w.PersR m M' y' z') : w.c M ≤ w.c M' := by
  obtain ⟨-, h2, -, -⟩ := h
  obtain ⟨-, -, h3', -⟩ := h'
  apply h3' M hM
  have hy'M : M ≠ y' := by rintro rfl; linarith
  rcases cbtw_or_cbtw (k := m) hy'M with hb | hb
  · exact hb
  · linarith [h2 y' hy' hb]

lemma le_of_persL {m M M' y z y' z' : ι} (hM : M ∈ w.C) (hy' : y' ∈ w.C)
    (hym' : w.c y' < w.c m) (hmM : w.c m < w.c M) (h : w.PersL m M y z)
    (h' : w.PersL m M' y' z') : w.c M ≤ w.c M' := by
  obtain ⟨h1, h2, -, -⟩ := h
  obtain ⟨-, -, h3', -⟩ := h'
  apply h3' M hM
  have hMm : M ≠ m := by rintro rfl; exact not_cbtw_right h1
  have hy'm : y' ≠ m := by rintro rfl; exact lt_irrefl _ hym'
  have hy'M : y' ≠ M := by rintro rfl; linarith
  rcases cbtw_total' (k := m) hy'm hMm hy'M with hb | hb
  · exact hb
  · linarith [h2 y' hy' hb]

lemma persR_persL_false {m M M' y z y' z' : ι} (hy : y ∈ w.C) (hz : z ∈ w.C) (hy' : y' ∈ w.C)
    (hz' : z' ∈ w.C) (hym : w.c y < w.c m) (hym' : w.c y' < w.c m) (hmM : w.c m < w.c M)
    (hmM' : w.c m < w.c M') (hMz : w.c M < w.c z) (hMz' : w.c M' < w.c z')
    (h : w.PersR m M y z) (h' : w.PersL m M' y' z') : False := by
  obtain ⟨-, -, h3, h4⟩ := h
  obtain ⟨-, -, h3', h4'⟩ := h'
  -- `e_z` lies between `e_{y'}` and `e_m`, and `e_{z'}` between `e_m` and `e_y`
  have e1 : cbtw y' z m := by
    have hy'm : y' ≠ m := by rintro rfl; exact lt_irrefl _ hym'
    have hzm : z ≠ m := by rintro rfl; linarith
    have hy'z : y' ≠ z := by rintro rfl; linarith
    rcases cbtw_total' (k := m) hy'm hzm hy'z with hb | hb
    · exact hb
    · linarith [h4 y' hy' hb]
  have e2 : cbtw m z' y := by
    have hz'y : z' ≠ y := by rintro rfl; linarith
    rcases cbtw_or_cbtw (k := m) hz'y with hb | hb
    · exact hb
    · linarith [h4' y hy hb]
  linarith [h3' z hz e1, h3 z' hz' e2]

/-- A minimum has at most one persistence partner. -/
lemma persPair_unique (hn : w.NoTC) {m M M' : ι} (h : w.PersPair m M) (h' : w.PersPair m M') :
    M = M' := by
  have u := (persPair_up h).2
  have u' := (persPair_up h').2
  obtain ⟨-, hM, hmM, y, hy, hym, z, hz, hMz, hRL⟩ := h
  obtain ⟨-, hM', hmM', y', hy', hym', z', hz', hMz', hRL'⟩ := h'
  have eq_of : w.c M = w.c M' → M = M' := fun e => by
    by_contra hne
    exact hn M M' ⟨hM, hM', hne, e, iff_of_true u u'⟩
  rcases hRL with hR | hL <;> rcases hRL' with hR' | hL'
  · exact eq_of (le_antisymm (le_of_persR hM hy' hym' hmM hR hR')
      (le_of_persR hM' hy hym hmM' hR' hR))
  · exact (persR_persL_false hy hz hy' hz' hym hym' hmM hmM' hMz hMz' hR hL').elim
  · exact (persR_persL_false hy' hz' hy hz hym' hym hmM' hmM hMz' hMz hR' hL).elim
  · exact eq_of (le_antisymm (le_of_persL hM hy' hym' hmM hL hL')
      (le_of_persL hM' hy hym hmM' hL' hL))

/-! ### Crimping two consecutive creases -/

/-- The creases of a sector of smallest angle form a persistence pair. -/
lemma persPair_consec {p : ι} (hp : p ∈ w.C)
    (hh : (w.c (prv w.C p) < w.c (nxt w.C p) ∧ w.c (nxt w.C p) < w.c p ∧
        w.c p < w.c (nxt w.C (nxt w.C p))) ∨
      (w.c (nxt w.C (nxt w.C p)) < w.c p ∧ w.c p < w.c (nxt w.C p) ∧
        w.c (nxt w.C p) < w.c (prv w.C p))) :
    w.PersPair p (nxt w.C p) ∨ w.PersPair (nxt w.C p) p := by
  have hq := w.nxt_mem hp
  have hu := w.prv_mem hp
  have hv := w.nxt_mem hq
  rcases hh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- `e_p` is a maximum, `e_{p+1}` a minimum
    right
    refine ⟨hq, hp, h2, prv w.C p, hu, h1, _, hv, h3, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · exact cbtw_nxt hu hp (w.prv_ne hp).symm
    · exact fun x hx hb => absurd hb ((nxt_spec w.nonempty p).2 x hx)
    · exact fun x hx hb => (eq_of_cbtw_prv_nxt hp hx hb).symm ▸ le_rfl
    · exact fun x hx hb => absurd hb ((nxt_spec w.nonempty _).2 x hx)
  · -- `e_p` is a minimum, `e_{p+1}` a maximum
    left
    refine ⟨hp, hq, h2, _, hv, h1, prv w.C p, hu, h3, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
    · exact cbtw_nxt hp hq (w.nxt_ne hp)
    · exact fun x hx hb => absurd hb ((nxt_spec w.nonempty p).2 x hx)
    · intro x hx hb
      exact (eq_of_cbtw_prv_nxt hq hx (by rw [prv_nxt hp]; exact hb)).symm ▸ le_rfl
    · exact fun x hx hb => absurd hb ((prv_spec w.nonempty p).2 x hx)

/-- The heights around a sector of smallest angle at a vertex without taco–taco rows: its two
creases lie strictly between the creases before and after them. -/
lemma heights_of_min (hn : w.NoTC) {a : ι} (ha : a ∈ w.C) (h3 : 3 ≤ w.C.card)
    (hmin : ∀ g ∈ w.C, w.len a ≤ w.len g) :
    (w.c (prv w.C (prv w.C a)) < w.c a ∧ w.c a < w.c (prv w.C a) ∧
        w.c (prv w.C a) < w.c (nxt w.C a)) ∨
      (w.c (nxt w.C a) < w.c (prv w.C a) ∧ w.c (prv w.C a) < w.c a ∧
        w.c a < w.c (prv w.C (prv w.C a))) := by
  obtain ⟨h1, h2⟩ := strict_of_noTC hn ha h3 hmin
  have hP := w.prv_mem ha
  have hnx := w.nxt_mem ha
  have hpa : nxt w.C (prv w.C a) = a := nxt_prv ha
  have hpn : prv w.C (nxt w.C a) = a := prv_nxt ha
  unfold len at h1 h2
  by_cases hu : w.up (prv w.C a)
  · have hua : ¬ w.up a := by
      have := up_nxt hP; rw [hpa] at this; exact fun h => this.1 h hu
    have hun : w.up (nxt w.C a) := (up_nxt ha).2 hua
    obtain ⟨l1, u1⟩ := lo_hi_of_not_up ha hua
    obtain ⟨l2, u2⟩ := lo_hi_of_up hu
    obtain ⟨l3, u3⟩ := lo_hi_of_up hun
    rw [hpn] at l3
    have : w.c a < w.c (prv w.C a) := by
      have := (up_iff_nxt hP).1 hu; rwa [hpa] at this
    left
    refine ⟨by linarith, this, by linarith⟩
  · have hua : w.up a := by
      have := up_nxt hP; rw [hpa] at this; exact this.2 hu
    have hun : ¬ w.up (nxt w.C a) := fun h => (up_nxt ha).1 h hua
    obtain ⟨l1, u1⟩ := lo_hi_of_up hua
    obtain ⟨l2, u2⟩ := lo_hi_of_not_up hP hu
    obtain ⟨l3, u3⟩ := lo_hi_of_not_up hnx hun
    rw [hpn] at u3
    have : w.c (prv w.C a) < w.c a := hua
    right
    refine ⟨by linarith, this, by linarith⟩

/-- The crimp of the two consecutive creases `p, nxt p`, whose heights lie strictly between
those of `prv p` and `nxt (nxt p)`: `w'` keeps the other creases and all positions. -/
structure CrimpPair (w w' : Walk ι α) (p : ι) : Prop where
  hp : p ∈ w.C
  h4 : 4 ≤ w.C.card
  hC : w'.C = (w.C.erase p).erase (nxt w.C p)
  hc : w'.c = w.c
  hh : (w.c (prv w.C p) < w.c (nxt w.C p) ∧ w.c (nxt w.C p) < w.c p ∧
        w.c p < w.c (nxt w.C (nxt w.C p))) ∨
      (w.c (nxt w.C (nxt w.C p)) < w.c p ∧ w.c p < w.c (nxt w.C p) ∧
        w.c (nxt w.C p) < w.c (prv w.C p))

namespace CrimpPair

variable {w' : Walk ι α} {p : ι} (P : CrimpPair w w' p)
include P

lemma sub {x : ι} (hx : x ∈ w'.C) : x ∈ w.C := by
  rw [P.hC] at hx; exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)

lemma ne {x : ι} (hx : x ∈ w'.C) : x ≠ p ∧ x ≠ nxt w.C p := by
  rw [P.hC] at hx
  exact ⟨(Finset.mem_erase.1 (Finset.mem_of_mem_erase hx)).1, (Finset.mem_erase.1 hx).1⟩

lemma cases {x : ι} (hx : x ∈ w.C) : x ∈ w'.C ∨ x = p ∨ x = nxt w.C p := by
  by_cases h1 : x = p
  · exact Or.inr (Or.inl h1)
  by_cases h2 : x = nxt w.C p
  · exact Or.inr (Or.inr h2)
  left; rw [P.hC]; exact Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hx⟩⟩

lemma prv_mem' : prv w.C p ∈ w'.C := by
  rw [P.hC]
  exact Finset.mem_erase.2 ⟨(nxt_ne_prv P.hp (by have := P.h4; omega)).symm,
    Finset.mem_erase.2 ⟨w.prv_ne P.hp, w.prv_mem P.hp⟩⟩

lemma nxt_mem' : nxt w.C (nxt w.C p) ∈ w'.C := by
  have hq := w.nxt_mem P.hp
  rw [P.hC]
  refine Finset.mem_erase.2 ⟨w.nxt_ne hq, Finset.mem_erase.2 ⟨fun h => ?_, w.nxt_mem hq⟩⟩
  have := card_le_two_of_nxt_nxt P.hp h
  have := P.h4
  omega

lemma lt_of_le {x : ι} (hx : x = p ∨ x = nxt w.C p) {A : α} (hu : A ≤ w.c (prv w.C p))
    (hv : A ≤ w.c (nxt w.C (nxt w.C p))) : A < w.c x := by
  rcases P.hh with h | h <;> rcases hx with rfl | rfl <;> linarith [h.1, h.2.1, h.2.2]

lemma lt_of_ge {x : ι} (hx : x = p ∨ x = nxt w.C p) {A : α} (hu : w.c (prv w.C p) ≤ A)
    (hv : w.c (nxt w.C (nxt w.C p)) ≤ A) : w.c x < A := by
  rcases P.hh with h | h <;> rcases hx with rfl | rfl <;> linarith [h.1, h.2.1, h.2.2]

/-- The outer neighbours of the crimped creases lie on the closed arc of any arc between two
surviving creases that contains one of them. -/
lemma outer {a b x : ι} (ha : a ∈ w'.C) (hb : b ∈ w'.C) (hx : x = p ∨ x = nxt w.C p)
    (hab : cbtw a x b) :
    (prv w.C p = a ∨ cbtw a (prv w.C p) b) ∧
      (nxt w.C (nxt w.C p) = b ∨ cbtw a (nxt w.C (nxt w.C p)) b) := by
  obtain ⟨hap, haq⟩ := P.ne ha
  obtain ⟨hbp, hbq⟩ := P.ne hb
  have hab' : cbtw a p b ∨ cbtw a (nxt w.C p) b := by
    rcases hx with rfl | rfl
    exacts [Or.inl hab, Or.inr hab]
  exact crimp_between P.hp (P.sub ha) (P.sub hb) hap haq hbp hbq hab'

/-- A strict lower bound on the creases of an arc survives the crimp, if it holds weakly at
the ends of the arc. -/
lemma low {a b : ι} (ha : a ∈ w'.C) (hb : b ∈ w'.C) {A : α} (hA : A ≤ w.c a) (hB : A ≤ w.c b)
    (h : ∀ x ∈ w'.C, cbtw a x b → A < w.c x) : ∀ x ∈ w.C, cbtw a x b → A < w.c x := by
  intro x hx hab
  rcases P.cases hx with hx' | hx'
  · exact h x hx' hab
  obtain ⟨hu, hv⟩ := P.outer ha hb hx' hab
  refine P.lt_of_le hx' ?_ ?_
  · rcases hu with e | e
    · rw [e]; exact hA
    · exact (h _ P.prv_mem' e).le
  · rcases hv with e | e
    · rw [e]; exact hB
    · exact (h _ P.nxt_mem' e).le

/-- An upper bound on the creases of an arc survives the crimp, if it holds at the ends. -/
lemma high {a b : ι} (ha : a ∈ w'.C) (hb : b ∈ w'.C) {A : α} (hA : w.c a ≤ A) (hB : w.c b ≤ A)
    (h : ∀ x ∈ w'.C, cbtw a x b → w.c x ≤ A) : ∀ x ∈ w.C, cbtw a x b → w.c x ≤ A := by
  intro x hx hab
  rcases P.cases hx with hx' | hx'
  · exact h x hx' hab
  obtain ⟨hu, hv⟩ := P.outer ha hb hx' hab
  refine (P.lt_of_ge hx' ?_ ?_).le
  · rcases hu with e | e
    · rw [e]; exact hA
    · exact h _ P.prv_mem' e
  · rcases hv with e | e
    · rw [e]; exact hB
    · exact h _ P.nxt_mem' e

/-- Persistence pairs of the crimped walk are persistence pairs of the walk. -/
lemma persPair {m M : ι} (h : w'.PersPair m M) : w.PersPair m M := by
  obtain ⟨hm, hM, hmM, y, hy, hym, z, hz, hMz, hRL⟩ := h
  have hc := P.hc
  rw [hc] at hmM hym hMz
  refine ⟨P.sub hm, P.sub hM, hmM, y, P.sub hy, hym, z, P.sub hz, hMz, ?_⟩
  rcases hRL with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · rw [hc] at h2 h3 h4
    exact Or.inl ⟨h1, P.low hm hM le_rfl hmM.le h2,
      P.high hm hy hmM.le (by linarith) h3, P.low hz hm (by linarith) le_rfl h4⟩
  · rw [hc] at h2 h3 h4
    exact Or.inr ⟨h1, P.low hM hm hmM.le le_rfl h2,
      P.high hy hm (by linarith) hmM.le h3, P.low hm hz le_rfl (by linarith) h4⟩

/-- The essential pair of the crimped walk is the essential pair of the walk. -/
lemma essential {a b : ι} (h : w'.Essential a b) : w.Essential a b := by
  obtain ⟨ha, hb, hT, hB⟩ := h
  have hc := P.hc
  rw [hc] at hT hB
  refine ⟨P.sub ha, P.sub hb, fun k hk => ?_, fun k hk => ?_⟩
  · rcases P.cases hk with hk' | hk'
    · exact hT k hk'
    · exact (P.lt_of_ge hk' (hT _ P.prv_mem') (hT _ P.nxt_mem')).le
  · rcases P.cases hk with hk' | hk'
    · exact hB k hk'
    · exact (P.lt_of_le hk' (hB _ P.prv_mem') (hB _ P.nxt_mem')).le

end CrimpPair

/-! ### The theorem -/

/-- With two creases, the two creases are the essential pair. -/
lemma essential_of_two (h2 : w.C.card = 2) {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C)
    (hab : a ≠ b) : w.Essential a b ∨ w.Essential b a := by
  have hC : ∀ x ∈ w.C, x = a ∨ x = b := by
    intro x hx
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
  have hne : w.c b ≠ w.c a := by rw [← nxt_of_two h2 ha hb hab]; exact c_nxt_ne ha
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · left
    refine ⟨ha, hb, fun k hk => ?_, fun k hk => ?_⟩ <;>
      rcases hC k hk with rfl | rfl <;> linarith
  · right
    refine ⟨hb, ha, fun k hk => ?_, fun k hk => ?_⟩ <;>
      rcases hC k hk with rfl | rfl <;> linarith

/-- **The pairs are persistence pairs**, by crimping a sector of smallest angle. -/
theorem pers_of_sameComp : ∀ (n : ℕ) (w : Walk ι α), w.C.card = n → w.NoTC →
    ∀ a ∈ w.C, ∀ b ∈ w.C, a ≠ b → w.SameComp a b →
      w.Essential a b ∨ w.Essential b a ∨ w.PersPair a b ∨ w.PersPair b a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hcard hn a ha b hb hab h
  by_cases h2c : w.C.card = 2
  · rcases essential_of_two h2c ha hb hab with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  have h4 : 4 ≤ w.C.card := by
    have := w.two_le; obtain ⟨m, hm⟩ := card_even (w := w); omega
  obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image w.C w.len w.nonempty
  have L := lemma5 hn ha₀ h4 hmin
  obtain ⟨⟨hpa, hcomp, -⟩, hC', hsame, -⟩ := L
  set R := runOfMin hn ha₀ h4 hmin
  set p := prv w.C a₀ with hp
  have hpC : p ∈ w.C := w.prv_mem ha₀
  have hnp : nxt w.C p = a₀ := nxt_prv ha₀
  have hh := heights_of_min hn ha₀ (by omega) hmin
  have P : CrimpPair w (w.runCrimp R) p :=
    { hp := hpC, h4 := h4, hC := by rw [hC', hnp], hc := runCrimp_c R,
      hh := by rw [hnp]; exact hh }
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
  have hcons := persPair_consec hpC P.hh
  rw [hnp] at hcons
  by_cases hab' : a = p ∨ a = a₀ ∨ b = p ∨ b = a₀
  · rcases hpair a ha b hb hab h hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hcons with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
    · rcases hcons with e | e
      · exact Or.inr (Or.inr (Or.inr e))
      · exact Or.inr (Or.inr (Or.inl e))
  push_neg at hab'
  have mem' : ∀ x ∈ w.C, x ≠ p → x ≠ a₀ → x ∈ (w.runCrimp R).C := by
    intro x hx' h1' h2'
    rw [hC']
    exact Finset.mem_erase.2 ⟨h2', Finset.mem_erase.2 ⟨h1', hx'⟩⟩
  have ha' := mem' a ha hab'.1 hab'.2.1
  have hb' := mem' b hb hab'.2.2.1 hab'.2.2.2
  have hcard' : (w.runCrimp R).C.card < n := by
    rw [hC', Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨(w.prv_ne ha₀).symm, ha₀⟩),
      Finset.card_erase_of_mem hpC]
    omega
  rcases ih _ hcard' (w.runCrimp R) rfl (noTC_runCrimp hn R) a ha' b hb' hab
      ((hsame a ha' b hb').1 h) with e | e | e | e
  · exact Or.inl (P.essential e)
  · exact Or.inr (Or.inl (P.essential e))
  · exact Or.inr (Or.inr (Or.inl (P.persPair e)))
  · exact Or.inr (Or.inr (Or.inr (P.persPair e)))

/-- The essential pair is a pair of Theorem 2. -/
lemma sameComp_of_essential (hn : w.NoTC) {a b : ι} (h : w.Essential a b) :
    w.SameComp a b := by
  obtain ⟨ha, hb, hT, hB⟩ := h
  by_cases h2 : w.C.card = 2
  · exact sameComp_of_two h2 ha hb
  have h3 : 3 ≤ w.C.card := by have := w.two_le; omega
  have := (pairing hn h3 hb ha hB hT).2.1
  have hb' : b ∈ w.C.filter (w.SameComp a) := by rw [this]; simp
  exact (Finset.mem_filter.1 hb').2

/-- Every persistence pair is a pair of Theorem 2. -/
lemma sameComp_of_persPair (hn : w.NoTC) {m M : ι} (h : w.PersPair m M) : w.SameComp m M := by
  have hu := persPair_up h
  obtain ⟨hm, hM, hmM, y, hy, hym, z, hz, hMz, -⟩ := id h
  by_cases h2 : w.C.card = 2
  · exact sameComp_of_two h2 hm hM
  have h3 : 3 ≤ w.C.card := by have := w.two_le; omega
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_ne
    (by rw [(card_sameComp hn h3 hm).1]; norm_num : 1 < (w.C.filter (w.SameComp m)).card) m
  obtain ⟨hjC, hs⟩ := Finset.mem_filter.1 hj
  rcases pers_of_sameComp _ w rfl hn m hm j hjC (Ne.symm hjm) hs with e | e | e | e
  · linarith [e.2.2.1 z hz]
  · linarith [e.2.2.2 y hy]
  · rwa [persPair_unique hn e h] at hs
  · exact absurd (persPair_up e).2 hu.1

/-- **Theorem 3 (persistence).**  At a vertex without taco–taco rows, two distinct creases are
paired by the rows (Theorem 2) if and only if they are the essential pair (a highest and a
lowest crease) or a persistence pair of the heights, given by the elder rule. -/
theorem persistence (hn : w.NoTC) {a b : ι} (ha : a ∈ w.C) (hb : b ∈ w.C) (hab : a ≠ b) :
    w.SameComp a b ↔
      w.Essential a b ∨ w.Essential b a ∨ w.PersPair a b ∨ w.PersPair b a := by
  refine ⟨pers_of_sameComp _ w rfl hn a ha b hb hab, ?_⟩
  rintro (e | e | e | e)
  · exact sameComp_of_essential hn e
  · exact conn_symm (sameComp_of_essential hn e)
  · exact sameComp_of_persPair hn e
  · exact conn_symm (sameComp_of_persPair hn e)

end Walk

end Origami
