import Origami.SumRows

/-!
# Crimping one sector, and lifting flat-folded states through a crimp

Crimping the sector `a` (Appendix B of the paper) merges `f_A = prv a`, `f_a` and
`f_Z = nxt a` into one sector, deleting the creases `A = prv a` and `a`.  In the
formalization the crimped walk has the crease set `(C.erase A).erase a`; the merged sector
keeps the name `Z` (it ends at the crease `Z`), and starts at `P = prv A`.

The crimp is legal when `f_a` is no longer than either neighbour (`CrimpOK`); this
includes the crimps of Lemma 6 and all the single crimps into which the run crimps of
Sec. 7 decompose.  The main result, `exists_lift`, is the constructive half of Hull's
analysis of crimps: a flat-folded state of the crimped walk lifts to one of the walk,
with the stack `f_A, f_a, f_Z` inserted where the merged sector was, in either of the two
orientations; the two deleted creases then receive opposite assignments, either way round.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

lemma zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  generalize z = u; revert u; decide

namespace Walk

variable {w : Walk ι α}

lemma len_of_up {g : ι} (h : w.up g) : w.len g = w.c g - w.c (prv w.C g) := by
  unfold len; rw [(lo_hi_of_up h).1, (lo_hi_of_up h).2]

lemma len_of_not_up {g : ι} (hg : g ∈ w.C) (h : ¬ w.up g) :
    w.len g = w.c (prv w.C g) - w.c g := by
  unfold len; rw [(lo_hi_of_not_up hg h).1, (lo_hi_of_not_up hg h).2]

/-- Maxima and minima alternate: there are as many of each. -/
lemma card_filter_up : (w.C.filter w.up).card = (w.C.filter (fun k => ¬ w.up k)).card := by
  apply Finset.card_bij (fun k _ => nxt w.C k)
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨w.nxt_mem hk.1, fun h => (up_nxt hk.1).1 h hk.2⟩
  · intro a ha b hb h
    exact nxt_injOn (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) h
  · intro l hl
    simp only [Finset.mem_filter] at hl
    refine ⟨prv w.C l, Finset.mem_filter.2 ⟨w.prv_mem hl.1, (up_prv hl.1).2 hl.2⟩,
      nxt_prv hl.1⟩

/-- A closed walk has even length. -/
lemma card_even : Even w.C.card := by
  have := Finset.card_filter_add_card_filter_not (s := w.C) w.up
  rw [← card_filter_up] at this
  exact ⟨_, this.symm⟩

/-- The hypotheses for crimping the sector `a`. -/
structure CrimpOK (w : Walk ι α) (a : ι) : Prop where
  mem : a ∈ w.C
  four : 4 ≤ w.C.card
  le_prv : w.len a ≤ w.len (prv w.C a)
  le_nxt : w.len a ≤ w.len (nxt w.C a)

namespace CrimpOK

variable {a : ι} (hc : w.CrimpOK a)
include hc

lemma memA : prv w.C a ∈ w.C := w.prv_mem hc.mem
lemma memP : prv w.C (prv w.C a) ∈ w.C := w.prv_mem hc.memA
lemma memZ : nxt w.C a ∈ w.C := w.nxt_mem hc.mem
lemma memN : nxt w.C (nxt w.C a) ∈ w.C := w.nxt_mem hc.memZ

lemma A_ne_a : prv w.C a ≠ a := w.prv_ne hc.mem
lemma Z_ne_a : nxt w.C a ≠ a := w.nxt_ne hc.mem
lemma A_ne_Z : prv w.C a ≠ nxt w.C a := (nxt_ne_prv hc.mem (by have := hc.four; omega)).symm
lemma P_ne_A : prv w.C (prv w.C a) ≠ prv w.C a := w.prv_ne hc.memA

lemma P_ne_a : prv w.C (prv w.C a) ≠ a := by
  intro h
  have h1 : nxt w.C a = prv w.C a := by have := nxt_prv hc.memA; rwa [h] at this
  have e : nxt w.C (nxt w.C a) = a := by rw [h1, nxt_prv hc.mem]
  have := card_le_two_of_nxt_nxt hc.mem e
  have := hc.four; omega

lemma P_ne_Z : prv w.C (prv w.C a) ≠ nxt w.C a := by
  intro h
  have h1 : nxt w.C (nxt w.C a) = prv w.C a := by rw [← h, nxt_prv hc.memA]
  have e : (nxt w.C)^[3] (nxt w.C a) = nxt w.C a := by
    show nxt w.C (nxt w.C (nxt w.C (nxt w.C a))) = nxt w.C a
    rw [h1, nxt_prv hc.mem]
  have := card_le_of_iterate hc.memZ (by norm_num) e
  have := hc.four; omega

lemma N_ne_a : nxt w.C (nxt w.C a) ≠ a := by
  intro h
  have := card_le_two_of_nxt_nxt hc.mem h
  have := hc.four; omega

lemma N_ne_A : nxt w.C (nxt w.C a) ≠ prv w.C a := by
  intro h
  have e : (nxt w.C)^[3] (prv w.C a) = prv w.C a := by
    show nxt w.C (nxt w.C (nxt w.C (prv w.C a))) = prv w.C a
    rw [nxt_prv hc.mem, h]
  have := card_le_of_iterate hc.memA (by norm_num) e
  have := hc.four; omega

lemma N_ne_Z : nxt w.C (nxt w.C a) ≠ nxt w.C a := w.nxt_ne hc.memZ

/-- The positions around a legal crimp, in one of the two orientations. -/
lemma pos :
    (w.up (prv w.C a) ∧ w.c (prv w.C (prv w.C a)) ≤ w.c a ∧ w.c a < w.c (prv w.C a) ∧
      w.c (prv w.C a) ≤ w.c (nxt w.C a) ∧ w.c (prv w.C (prv w.C a)) < w.c (prv w.C a) ∧
      w.c a < w.c (nxt w.C a)) ∨
    (¬ w.up (prv w.C a) ∧ w.c a ≤ w.c (prv w.C (prv w.C a)) ∧ w.c (prv w.C a) < w.c a ∧
      w.c (nxt w.C a) ≤ w.c (prv w.C a) ∧ w.c (prv w.C a) < w.c (prv w.C (prv w.C a)) ∧
      w.c (nxt w.C a) < w.c a) := by
  have hA := hc.memA; have ha := hc.mem; have hZ := hc.memZ
  have upa : w.up a ↔ ¬ w.up (prv w.C a) := by
    have := up_nxt hA; rwa [nxt_prv ha] at this
  have upZ : w.up (nxt w.C a) ↔ ¬ w.up a := up_nxt ha
  have l1 := hc.le_prv; have l2 := hc.le_nxt
  by_cases hu : w.up (prv w.C a)
  · left
    have hna : ¬ w.up a := fun h => upa.1 h hu
    have hz : w.up (nxt w.C a) := upZ.2 hna
    rw [len_of_not_up ha hna, len_of_up hu] at l1
    rw [len_of_not_up ha hna, len_of_up hz, prv_nxt ha] at l2
    have e1 : w.c a < w.c (prv w.C a) := (not_up_iff ha).1 hna
    have e2 : w.c a < w.c (nxt w.C a) := (not_up_iff_nxt ha).1 hna
    have e3 : w.c (prv w.C (prv w.C a)) < w.c (prv w.C a) := hu
    refine ⟨hu, by linarith, e1, by linarith, e3, e2⟩
  · right
    have hna : w.up a := upa.2 hu
    have hz : ¬ w.up (nxt w.C a) := fun h => upZ.1 h hna
    rw [len_of_up hna, len_of_not_up hA hu] at l1
    rw [len_of_up hna, len_of_not_up hZ hz, prv_nxt ha] at l2
    have e1 : w.c (prv w.C a) < w.c a := hna
    have e2 : w.c (nxt w.C a) < w.c a := (up_iff_nxt ha).1 hna
    have e3 : w.c (prv w.C a) < w.c (prv w.C (prv w.C a)) := (not_up_iff hA).1 hu
    refine ⟨hu, by linarith, e1, by linarith, e3, e2⟩

end CrimpOK

/-- The crease set of the crimped walk. -/
def crimpC (w : Walk ι α) (a : ι) : Finset ι := (w.C.erase (prv w.C a)).erase a

lemma crimpC_eq {a : ι} (ha : a ∈ w.C) :
    w.crimpC a = (w.C.erase (prv w.C a)).erase (nxt w.C (prv w.C a)) := by
  rw [crimpC, nxt_prv ha]

lemma mem_crimpC {a k : ι} : k ∈ w.crimpC a ↔ k ≠ a ∧ k ≠ prv w.C a ∧ k ∈ w.C := by
  simp [crimpC, Finset.mem_erase]

lemma card_crimpC {a : ι} (hc : w.CrimpOK a) : (w.crimpC a).card = w.C.card - 2 := by
  rw [crimpC, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hc.A_ne_a.symm, hc.mem⟩),
    Finset.card_erase_of_mem hc.memA]
  omega

lemma crimpC_nxt {a k : ι} (hc : w.CrimpOK a) (hk : k ∈ w.crimpC a) :
    nxt (w.crimpC a) k = if k = prv w.C (prv w.C a) then nxt w.C a else nxt w.C k := by
  have := nxt_erase_pair hc.memA hc.four (by rwa [← crimpC_eq hc.mem])
  rw [← crimpC_eq hc.mem, nxt_prv hc.mem] at this
  exact this

lemma crimpC_prv {a k : ι} (hc : w.CrimpOK a) (hk : k ∈ w.crimpC a) :
    prv (w.crimpC a) k = if k = nxt w.C a then prv w.C (prv w.C a) else prv w.C k := by
  have := prv_erase_pair hc.memA hc.four (by rwa [← crimpC_eq hc.mem])
  rw [← crimpC_eq hc.mem, nxt_prv hc.mem] at this
  exact this

/-- The walk obtained by crimping the sector `a`. -/
def crimp (w : Walk ι α) (a : ι) (hc : w.CrimpOK a) : Walk ι α where
  C := w.crimpC a
  c := w.c
  two_le := by rw [card_crimpC hc]; have := hc.four; omega
  zig := by
    intro k hk
    rw [crimpC_nxt hc hk, crimpC_prv hc hk]
    have hkC := (mem_crimpC.1 hk).2.2
    by_cases hP : k = prv w.C (prv w.C a)
    · rw [if_pos hP, if_neg (hP ▸ hc.P_ne_Z)]
      subst hP
      have z := w.zig _ hc.memP
      rw [nxt_prv hc.memA] at z
      rcases hc.pos with ⟨-, p1, p2, p3, p4, -⟩ | ⟨-, p1, p2, p3, p4, -⟩
      · right; exact ⟨(z.resolve_left (fun h => by linarith [h.2])).1, by linarith⟩
      · left; exact ⟨(z.resolve_right (fun h => by linarith [h.2])).1, by linarith⟩
    · rw [if_neg hP]
      by_cases hZ : k = nxt w.C a
      · rw [if_pos hZ]
        subst hZ
        have z := w.zig _ hc.memZ
        rw [prv_nxt hc.mem] at z
        rcases hc.pos with ⟨-, p1, p2, p3, p4, p5⟩ | ⟨-, p1, p2, p3, p4, p5⟩
        · left; exact ⟨by linarith, (z.resolve_right (fun h => by linarith [h.1])).2⟩
        · right; exact ⟨by linarith, (z.resolve_left (fun h => by linarith [h.1])).2⟩
      · rw [if_neg hZ]; exact w.zig k hkC

@[simp] lemma crimp_C {a : ι} (hc : w.CrimpOK a) : (w.crimp a hc).C = w.crimpC a := rfl
@[simp] lemma crimp_c {a : ι} (hc : w.CrimpOK a) : (w.crimp a hc).c = w.c := rfl

namespace CrimpOK

variable {a : ι} (hc : w.CrimpOK a)
include hc

lemma mem_C' {k : ι} (hk : k ∈ w.C) (h1 : k ≠ a) (h2 : k ≠ prv w.C a) : k ∈ (w.crimp a hc).C :=
  mem_crimpC.2 ⟨h1, h2, hk⟩

lemma memZ' : nxt w.C a ∈ (w.crimp a hc).C := hc.mem_C' hc.memZ hc.Z_ne_a hc.A_ne_Z.symm
lemma memP' : prv w.C (prv w.C a) ∈ (w.crimp a hc).C := hc.mem_C' hc.memP hc.P_ne_a hc.P_ne_A

lemma nxt' {k : ι} (hk : k ∈ (w.crimp a hc).C) :
    nxt (w.crimp a hc).C k = if k = prv w.C (prv w.C a) then nxt w.C a else nxt w.C k :=
  crimpC_nxt hc hk

lemma prv' {k : ι} (hk : k ∈ (w.crimp a hc).C) :
    prv (w.crimp a hc).C k = if k = nxt w.C a then prv w.C (prv w.C a) else prv w.C k :=
  crimpC_prv hc hk

/-- Crimping does not change the type of the surviving creases. -/
lemma up' {k : ι} (hk : k ∈ (w.crimp a hc).C) : (w.crimp a hc).up k ↔ w.up k := by
  unfold up
  rw [hc.prv' hk, crimp_c]
  split_ifs with h
  · subst h
    rw [prv_nxt hc.mem]
    rcases hc.pos with ⟨-, p1, p2, p3, p4, p5⟩ | ⟨-, p1, p2, p3, p4, p5⟩
    · exact ⟨fun _ => p5, fun _ => by linarith⟩
    · exact ⟨fun h => by linarith, fun h => by linarith⟩
  · rfl

lemma lohi' {g : ι} (hg : g ≠ nxt w.C a) (hg' : g ∈ (w.crimp a hc).C) :
    (w.crimp a hc).lo g = w.lo g ∧ (w.crimp a hc).hi g = w.hi g := by
  unfold lo hi; rw [hc.prv' hg', if_neg hg]; exact ⟨rfl, rfl⟩

/-- The intervals of the three merged sectors and of the merged sector, in the two
orientations. -/
lemma intervals :
    let A := prv w.C a; let P := prv w.C A; let Z := nxt w.C a
    (w.lo A = w.c P ∧ w.hi A = w.c A ∧ w.lo a = w.c a ∧ w.hi a = w.c A ∧ w.lo Z = w.c a ∧
      w.hi Z = w.c Z ∧ (w.crimp a hc).lo Z = w.c P ∧ (w.crimp a hc).hi Z = w.c Z ∧
      w.c P ≤ w.c a ∧ w.c a < w.c A ∧ w.c A ≤ w.c Z) ∨
    (w.lo A = w.c A ∧ w.hi A = w.c P ∧ w.lo a = w.c A ∧ w.hi a = w.c a ∧ w.lo Z = w.c Z ∧
      w.hi Z = w.c a ∧ (w.crimp a hc).lo Z = w.c Z ∧ (w.crimp a hc).hi Z = w.c P ∧
      w.c a ≤ w.c P ∧ w.c A < w.c a ∧ w.c Z ≤ w.c A) := by
  intro A P Z
  have eZ : prv (w.crimp a hc).C Z = P := by rw [hc.prv' hc.memZ', if_pos rfl]
  have eZ' : prv w.C Z = a := prv_nxt hc.mem
  unfold lo hi
  rw [eZ, eZ', crimp_c]
  rcases hc.pos with ⟨-, p1, p2, p3, p4, p5⟩ | ⟨-, p1, p2, p3, p4, p5⟩
  · left
    refine ⟨min_eq_left p4.le, max_eq_right p4.le, min_eq_right p2.le, max_eq_left p2.le,
      min_eq_left p5.le, max_eq_right p5.le, min_eq_left (by linarith), max_eq_right (by linarith),
      p1, p2, p3⟩
  · right
    refine ⟨min_eq_right p4.le, max_eq_left p4.le, min_eq_left p2.le, max_eq_right p2.le,
      min_eq_right p5.le, max_eq_left p5.le, min_eq_right (by linarith), max_eq_left (by linarith),
      p1, p2, p3⟩

lemma block_inside {g : ι} (hg : g = prv w.C a ∨ g = a ∨ g = nxt w.C a) :
    (w.crimp a hc).lo (nxt w.C a) ≤ w.lo g ∧ w.hi g ≤ (w.crimp a hc).hi (nxt w.C a) := by
  rcases hc.intervals with ⟨i1, i2, i3, i4, i5, i6, i7, i8, p1, p2, p3⟩ |
    ⟨i1, i2, i3, i4, i5, i6, i7, i8, p1, p2, p3⟩ <;>
  rcases hg with rfl | rfl | rfl <;> simp only [i1, i2, i3, i4, i5, i6, i7, i8] <;>
    constructor <;> linarith

lemma not_TT_P {g : ι} (hg : g = prv w.C a ∨ g = a ∨ g = nxt w.C a) :
    ¬ w.IsTT (prv w.C (prv w.C a)) g := by
  rintro ⟨-, -, h1, h2⟩
  rcases hc.intervals with ⟨i1, i2, i3, i4, i5, i6, i7, i8, p1, p2, p3⟩ |
    ⟨i1, i2, i3, i4, i5, i6, i7, i8, p1, p2, p3⟩ <;>
  rcases hg with rfl | rfl | rfl <;> simp only [i1, i2, i3, i4, i5, i6] at h1 h2 <;> linarith

lemma not_TT_Z {g : ι} (hg : g = prv w.C a ∨ g = a ∨ g = nxt w.C a) :
    ¬ w.IsTT (nxt w.C a) g := by
  rintro ⟨-, -, h1, h2⟩
  rcases hc.intervals with ⟨i1, i2, i3, i4, i5, i6, i7, i8, p1, p2, p3⟩ |
    ⟨i1, i2, i3, i4, i5, i6, i7, i8, p1, p2, p3⟩ <;>
  rcases hg with rfl | rfl | rfl <;> simp only [i1, i2, i3, i4, i5, i6] at h1 h2 <;> linarith

end CrimpOK

/-! ### The lifted stack -/

/-- The sector of the crimped walk that contains a sector of the walk. -/
def base (w : Walk ι α) (a g : ι) : ι := if g = prv w.C a ∨ g = a then nxt w.C a else g

/-- Heights of the lifted stack: the merged sector is replaced by `f_A, f_a, f_Z`,
from bottom to top if `t`, from top to bottom otherwise. -/
def liftOff (w : Walk ι α) (a : ι) (t : Bool) (g : ι) : ℤ :=
  if g = prv w.C a then (if t then 0 else 2) else if g = a then 1
  else if g = nxt w.C a then (if t then 2 else 0) else 0

def liftH (w : Walk ι α) (a : ι) (h' : ι → ℤ) (t : Bool) (g : ι) : ℤ :=
  4 * h' (w.base a g) + w.liftOff a t g

namespace CrimpOK

variable {a : ι} (hc : w.CrimpOK a)
include hc

lemma base_mem {g : ι} (hg : g ∈ w.C) : w.base a g ∈ (w.crimp a hc).C := by
  unfold base; split_ifs with h
  · exact hc.memZ'
  · push_neg at h; exact hc.mem_C' hg h.2 h.1

lemma base_of_out {g : ι} (h1 : g ≠ prv w.C a) (h2 : g ≠ a) : w.base a g = g := by
  unfold base; rw [if_neg (by tauto)]

lemma base_A : w.base a (prv w.C a) = nxt w.C a := by unfold base; simp
lemma base_a : w.base a a = nxt w.C a := by unfold base; simp
lemma base_Z : w.base a (nxt w.C a) = nxt w.C a := hc.base_of_out hc.A_ne_Z.symm hc.Z_ne_a

lemma liftH_eq (h' : ι → ℤ) (t : Bool) (g : ι) :
    ∃ o, 0 ≤ o ∧ o ≤ 2 ∧ w.liftH a h' t g = 4 * h' (w.base a g) + o := by
  refine ⟨_, ?_, ?_, rfl⟩ <;> unfold liftOff <;> split_ifs <;> simp

lemma off_A (t : Bool) : w.liftOff a t (prv w.C a) = if t then 0 else 2 := by
  unfold liftOff; rw [if_pos rfl]

lemma off_a (t : Bool) : w.liftOff a t a = 1 := by
  unfold liftOff; rw [if_neg hc.A_ne_a.symm, if_pos rfl]

lemma off_Z (t : Bool) : w.liftOff a t (nxt w.C a) = if t then 2 else 0 := by
  unfold liftOff; rw [if_neg hc.A_ne_Z.symm, if_neg hc.Z_ne_a, if_pos rfl]

/-- Between different merged sectors, the lifted stack keeps the old order. -/
lemma xOf_liftH {h' : ι → ℤ} (hinj : Set.InjOn h' (w.crimp a hc).C) (t : Bool) {g g' : ι}
    (hg : g ∈ w.C) (hg' : g' ∈ w.C) (hb : w.base a g ≠ w.base a g') :
    xOf (w.liftH a h' t) g g' = xOf h' (w.base a g) (w.base a g') := by
  obtain ⟨o, o0, o2, e⟩ := hc.liftH_eq h' t g
  obtain ⟨o', o0', o2', e'⟩ := hc.liftH_eq h' t g'
  have hne : h' (w.base a g) ≠ h' (w.base a g') := fun h =>
    hb (hinj (hc.base_mem hg) (hc.base_mem hg') h)
  unfold xOf
  rw [e, e']
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg (not_lt.2 h.le), if_neg (by omega)]

lemma liftH_injOn {h' : ι → ℤ} (hinj : Set.InjOn h' (w.crimp a hc).C) (t : Bool) :
    Set.InjOn (w.liftH a h' t) w.C := by
  intro g hg g' hg' e
  by_cases hb : w.base a g = w.base a g'
  · unfold liftH at e
    rw [hb, add_right_inj] at e
    have oA := hc.off_A t; have oa := hc.off_a t; have oZ := hc.off_Z t
    by_cases h1 : g = prv w.C a ∨ g = a <;> by_cases h2 : g' = prv w.C a ∨ g' = a
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at e ⊢ <;>
        first | rfl | (rw [oA, oa] at e; cases t <;> simp at e)
    · have : g' = nxt w.C a := by rw [← hc.base_of_out (not_or.1 h2).1 (not_or.1 h2).2, ← hb,
        show w.base a g = nxt w.C a by unfold base; rw [if_pos h1]]
      rw [this, oZ] at e
      rcases h1 with h1 | h1 <;> rw [h1] at e
      · rw [oA] at e; cases t <;> simp at e
      · rw [oa] at e; cases t <;> simp at e
    · have : g = nxt w.C a := by rw [← hc.base_of_out (not_or.1 h1).1 (not_or.1 h1).2, hb,
        show w.base a g' = nxt w.C a by unfold base; rw [if_pos h2]]
      rw [this, oZ] at e
      rcases h2 with h2 | h2 <;> rw [h2] at e
      · rw [oA] at e; cases t <;> simp at e
      · rw [oa] at e; cases t <;> simp at e
    · rw [← hc.base_of_out (not_or.1 h1).1 (not_or.1 h1).2,
        ← hc.base_of_out (not_or.1 h2).1 (not_or.1 h2).2, hb]
  · exfalso
    obtain ⟨o, o0, o2, eo⟩ := hc.liftH_eq h' t g
    obtain ⟨o', o0', o2', eo'⟩ := hc.liftH_eq h' t g'
    rw [eo, eo'] at e
    have : h' (w.base a g) = h' (w.base a g') := by omega
    exact hb (hinj (hc.base_mem hg) (hc.base_mem hg') this)

/-- Inside the stack, `f_A` and `f_a` lie on the same side of `f_Z`. -/
lemma block_AZ (h' : ι → ℤ) (t : Bool) :
    xOf (w.liftH a h' t) (prv w.C a) (nxt w.C a) = xOf (w.liftH a h' t) a (nxt w.C a) := by
  unfold xOf liftH
  rw [hc.base_A, hc.base_a, hc.base_Z, hc.off_A, hc.off_a, hc.off_Z]
  cases t <;> simp

/-- Inside the stack, `f_a` and `f_Z` lie on the same side of `f_A`. -/
lemma block_aA (h' : ι → ℤ) (t : Bool) :
    xOf (w.liftH a h' t) a (prv w.C a) = xOf (w.liftH a h' t) (nxt w.C a) (prv w.C a) := by
  unfold xOf liftH
  rw [hc.base_A, hc.base_a, hc.base_Z, hc.off_A, hc.off_a, hc.off_Z]
  cases t <;> simp

/-- The two creases of the crimped sector receive the same layer value `t`. -/
lemma block_val (h' : ι → ℤ) (t : Bool) :
    xOf (w.liftH a h' t) (prv w.C a) a = (if t then 1 else 0) ∧
      xOf (w.liftH a h' t) a (nxt w.C a) = (if t then 1 else 0) := by
  unfold xOf liftH
  rw [hc.base_A, hc.base_a, hc.base_Z, hc.off_A, hc.off_a, hc.off_Z]
  cases t <;> simp

lemma isTC_symm {q l : ι} (h : w.IsTC q l) : w.IsTC l q :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

/-- A taco–taco row with one crease in the stack and the other outside holds. -/
lemma tc_block {h' : ι → ℤ} (hinj : Set.InjOn h' (w.crimp a hc).C) (t : Bool) {q l : ι}
    (hq : q = prv w.C a ∨ q = a) (hl : ¬ (l = prv w.C a ∨ l = a)) (htc : w.IsTC q l) :
    (Row.tc q (nxt w.C q) l (nxt w.C l)).eval (xOf (w.liftH a h' t)) = 0 := by
  rw [Row.eval_tc]
  obtain ⟨hqC, hlC, hne, hcq, hup⟩ := htc
  have hx := fun {g g'} (hg : g ∈ w.C) (hg' : g' ∈ w.C) hb => hc.xOf_liftH hinj t hg hg' hb
  have hlA : l ≠ prv w.C a := fun e => hl (Or.inl e)
  have hla : l ≠ a := fun e => hl (Or.inr e)
  have hnl := w.nxt_mem hlC
  by_cases hlP : l = prv w.C (prv w.C a)
  · subst hlP
    rcases hq with hq | hq
    · exfalso; have := up_prv hc.memA; rw [hq] at hup; tauto
    · rw [hq, nxt_prv hc.memA]
      have e1 : xOf (w.liftH a h' t) a (prv w.C (prv w.C a)) =
          xOf (w.liftH a h' t) (nxt w.C a) (prv w.C (prv w.C a)) := by
        rw [hx hc.mem hc.memP (by rw [hc.base_a, hc.base_of_out hlA hla]; exact hc.P_ne_Z.symm),
          hx hc.memZ hc.memP (by rw [hc.base_Z, hc.base_of_out hlA hla]; exact hc.P_ne_Z.symm),
          hc.base_a, hc.base_Z]
      rw [e1, zmod2_add_self, zero_add, hc.block_aA h' t, zmod2_add_self]
  by_cases hlZ : l = nxt w.C a
  · subst hlZ
    rcases hq with hq | hq
    · rw [hq, nxt_prv hc.mem]
      have e1 : xOf (w.liftH a h' t) (prv w.C a) (nxt w.C (nxt w.C a)) =
          xOf (w.liftH a h' t) a (nxt w.C (nxt w.C a)) := by
        have bN := hc.base_of_out hc.N_ne_A hc.N_ne_a
        have m1 : w.base a (prv w.C a) ≠ w.base a (nxt w.C (nxt w.C a)) := by
          rw [hc.base_A, bN]; exact hc.N_ne_Z.symm
        have m2 : w.base a a ≠ w.base a (nxt w.C (nxt w.C a)) := by
          rw [hc.base_a, bN]; exact hc.N_ne_Z.symm
        rw [hx hc.memA hc.memN m1, hx hc.mem hc.memN m2, hc.base_A, hc.base_a]
      rw [hc.block_AZ h' t, zmod2_add_self, zero_add, e1, zmod2_add_self]
    · exfalso; have := up_nxt hc.mem; rw [hq] at hup; tauto
  · have bq : w.base a q = nxt w.C a := by unfold base; rw [if_pos hq]
    have hnq : nxt w.C q ∈ w.C := w.nxt_mem hqC
    have bnq : w.base a (nxt w.C q) = nxt w.C a := by
      rcases hq with hq | hq
      · rw [hq, nxt_prv hc.mem]; exact hc.base_a
      · rw [hq]; exact hc.base_Z
    have hnlA : nxt w.C l ≠ prv w.C a := fun e => hlP (by rw [← prv_nxt hlC, e])
    have hnla : nxt w.C l ≠ a := fun e => hlA (by rw [← prv_nxt hlC, e])
    have bl : w.base a l = l := hc.base_of_out hlA hla
    have bnl : w.base a (nxt w.C l) = nxt w.C l := hc.base_of_out hnlA hnla
    have hlZ' : nxt w.C l ≠ nxt w.C a := fun e => hla (nxt_injOn hlC hc.mem e)
    have n1 : w.base a q ≠ w.base a l := by rw [bq, bl]; exact Ne.symm hlZ
    have n2 : w.base a (nxt w.C q) ≠ w.base a l := by rw [bnq, bl]; exact Ne.symm hlZ
    have n3 : w.base a q ≠ w.base a (nxt w.C l) := by rw [bq, bnl]; exact Ne.symm hlZ'
    have n4 : w.base a (nxt w.C q) ≠ w.base a (nxt w.C l) := by rw [bnq, bnl]; exact Ne.symm hlZ'
    rw [hx hqC hlC n1, hx hnq hlC n2, hx hqC hnl n3, hx hnq hnl n4, bq, bnq, zmod2_add_self,
      zero_add, zmod2_add_self]

lemma base_nxt {q : ι} (hq : q ∈ w.C) (hqA : q ≠ prv w.C a) (hqa : q ≠ a) :
    w.base a (nxt w.C q) = nxt (w.crimp a hc).C q := by
  rw [hc.nxt' (hc.mem_C' hq hqa hqA)]
  split_ifs with hqP
  · rw [hqP, nxt_prv hc.memA]; exact hc.base_A
  · exact hc.base_of_out (fun e => hqP (by rw [← prv_nxt hq, e]))
      (fun e => hqA (by rw [← prv_nxt hq, e]))

/-- **The lifted stack is a flat-folded state**: it satisfies every row of the walk. -/
theorem liftH_isSol {h' : ι → ℤ} (hf : (w.crimp a hc).IsFlat h') (t : Bool) :
    w.IsSol (xOf (w.liftH a h' t)) := by
  obtain ⟨hinj, hsol⟩ := hf
  have hx := fun {g g'} (hg : g ∈ w.C) (hg' : g' ∈ w.C) hb => hc.xOf_liftH hinj t hg hg' hb
  have hanti : w.Antisymm (xOf (w.liftH a h' t)) := antisymm_xOf (hc.liftH_injOn hinj t)
  intro r hr
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, hqg, rfl⟩ := mem_ttRows.1 hr
    obtain ⟨d1, d2⟩ := tt_distinct hqg
    obtain ⟨hq, hg, i1, i2⟩ := hqg
    rw [Row.eval_tt]
    by_cases hgQ : g = prv w.C a ∨ g = a ∨ g = nxt w.C a
    · by_cases hqP : q = prv w.C (prv w.C a)
      · subst hqP; exact absurd ⟨hq, hg, i1, i2⟩ (hc.not_TT_P hgQ)
      by_cases hqZ : q = nxt w.C a
      · subst hqZ; exact absurd ⟨hq, hg, i1, i2⟩ (hc.not_TT_Z hgQ)
      by_cases hqA : q = prv w.C a
      · have hgZ : g = nxt w.C a := by
          rcases hgQ with h | h | h
          · exact absurd (hqA.trans h.symm) d1
          · exact absurd (by rw [hqA, nxt_prv hc.mem, h]) d2
          · exact h
        rw [hqA, nxt_prv hc.mem, hgZ, hc.block_AZ h' t, zmod2_add_self]
      by_cases hqa : q = a
      · have hgA : g = prv w.C a := by
          rcases hgQ with h | h | h
          · exact h
          · exact absurd (hqa.trans h.symm) d1
          · exact absurd (by rw [hqa, h]) d2
        rw [hqa, hgA, hc.block_aA h' t, zmod2_add_self]
      -- an outer crease inside the merged sector
      have hnA : nxt w.C q ≠ prv w.C a := fun e => hqP (by rw [← prv_nxt hq, e])
      have hna : nxt w.C q ≠ a := fun e => hqA (by rw [← prv_nxt hq, e])
      have hnZ : nxt w.C q ≠ nxt w.C a := fun e => hqa (nxt_injOn hq hc.mem e)
      have bg : w.base a g = nxt w.C a := by
        rcases hgQ with h | h | h <;> rw [h]
        · exact hc.base_A
        · exact hc.base_a
        · exact hc.base_Z
      have bq : w.base a q = q := hc.base_of_out hqA hqa
      have bnq : w.base a (nxt w.C q) = nxt w.C q := hc.base_of_out hnA hna
      have hqC' : q ∈ (w.crimp a hc).C := hc.mem_C' hq hqa hqA
      have htt : (w.crimp a hc).IsTT q (nxt w.C a) :=
        ⟨hqC', hc.memZ', lt_of_le_of_lt (hc.block_inside hgQ).1 i1,
          lt_of_lt_of_le i2 (hc.block_inside hgQ).2⟩
      have hrow := hsol _ (tt_mem_rows htt)
      rw [Row.eval_tt, hc.nxt' hqC', if_neg hqP] at hrow
      have m1 : w.base a q ≠ w.base a g := by rw [bq, bg]; exact hqZ
      have m2 : w.base a (nxt w.C q) ≠ w.base a g := by rw [bnq, bg]; exact hnZ
      rw [hx hq hg m1, hx (w.nxt_mem hq) hg m2, bq, bnq, bg]
      exact hrow
    · push_neg at hgQ
      have bg : w.base a g = g := hc.base_of_out hgQ.1 hgQ.2.1
      have hgC' : g ∈ (w.crimp a hc).C := hc.mem_C' hg hgQ.2.1 hgQ.1
      by_cases hqAa : q = prv w.C a ∨ q = a
      · have bq : w.base a q = nxt w.C a := by unfold base; rw [if_pos hqAa]
        have bnq : w.base a (nxt w.C q) = nxt w.C a := by
          rcases hqAa with e | e
          · rw [e, nxt_prv hc.mem]; exact hc.base_a
          · rw [e]; exact hc.base_Z
        have m1 : w.base a q ≠ w.base a g := by rw [bq, bg]; exact Ne.symm hgQ.2.2
        have m2 : w.base a (nxt w.C q) ≠ w.base a g := by rw [bnq, bg]; exact Ne.symm hgQ.2.2
        rw [hx hq hg m1, hx (w.nxt_mem hq) hg m2, bq, bnq, zmod2_add_self]
      · push_neg at hqAa
        have hqC' : q ∈ (w.crimp a hc).C := hc.mem_C' hq hqAa.2 hqAa.1
        have bq : w.base a q = q := hc.base_of_out hqAa.1 hqAa.2
        have bnq := hc.base_nxt hq hqAa.1 hqAa.2
        have lh := hc.lohi' hgQ.2.2 hgC'
        have htt : (w.crimp a hc).IsTT q g :=
          ⟨hqC', hgC', by rw [lh.1]; exact i1, by rw [lh.2]; exact i2⟩
        obtain ⟨-, e2⟩ := tt_distinct htt
        have hrow := hsol _ (tt_mem_rows htt)
        rw [Row.eval_tt] at hrow
        have m1 : w.base a q ≠ w.base a g := by rw [bq, bg]; exact d1
        have m2 : w.base a (nxt w.C q) ≠ w.base a g := by rw [bnq, bg]; exact e2
        rw [hx hq hg m1, hx (w.nxt_mem hq) hg m2, bq, bnq, bg]
        exact hrow
  · obtain ⟨q, l, hql, htc, rfl⟩ := mem_tcRows.1 hr
    by_cases hq : q = prv w.C a ∨ q = a
    · by_cases hl : l = prv w.C a ∨ l = a
      · exfalso
        obtain ⟨-, -, hne, -, hup⟩ := htc
        have := up_nxt hc.memA; rw [nxt_prv hc.mem] at this
        rcases hq with e | e <;> rcases hl with f | f <;> rw [e, f] at hup hne <;> tauto
      · exact hc.tc_block hinj t hq hl htc
    · by_cases hl : l = prv w.C a ∨ l = a
      · -- exchange the two creases of the row
        obtain ⟨d1, d2, d3, d4⟩ := tc_distinct htc
        have hqC := htc.1; have hlC := htc.2.1
        have hs := hc.tc_block hinj t hl hq (hc.isTC_symm htc)
        rw [Row.eval_tc] at hs ⊢
        rw [hanti _ hqC _ hlC d1, hanti _ (w.nxt_mem hqC) _ hlC d3,
          hanti _ hqC _ (w.nxt_mem hlC) d2, hanti _ (w.nxt_mem hqC) _ (w.nxt_mem hlC) d4] at hs
        revert hs
        generalize xOf (w.liftH a h' t) q l = u1
        generalize xOf (w.liftH a h' t) (nxt w.C q) l = u2
        generalize xOf (w.liftH a h' t) q (nxt w.C l) = u3
        generalize xOf (w.liftH a h' t) (nxt w.C q) (nxt w.C l) = u4
        revert u1 u2 u3 u4; decide
      · -- a row of the crimped walk
        push_neg at hq hl
        obtain ⟨hqC, hlC, hne, hcq, hup⟩ := htc
        have hqC' := hc.mem_C' hqC hq.2 hq.1
        have hlC' := hc.mem_C' hlC hl.2 hl.1
        have htc' : (w.crimp a hc).IsTC q l :=
          ⟨hqC', hlC', hne, hcq, by rw [hc.up' hqC', hc.up' hlC']; exact hup⟩
        obtain ⟨d1, d2, d3, d4⟩ := tc_distinct htc'
        have hrow := hsol _ (tc_mem_rows hql htc')
        rw [Row.eval_tc] at hrow ⊢
        have bq : w.base a q = q := hc.base_of_out hq.1 hq.2
        have bl : w.base a l = l := hc.base_of_out hl.1 hl.2
        have bnq := hc.base_nxt hqC hq.1 hq.2
        have bnl := hc.base_nxt hlC hl.1 hl.2
        have m1 : w.base a q ≠ w.base a l := by rw [bq, bl]; exact d1
        have m2 : w.base a (nxt w.C q) ≠ w.base a l := by rw [bnq, bl]; exact d3
        have m3 : w.base a q ≠ w.base a (nxt w.C l) := by rw [bq, bnl]; exact d2
        have m4 : w.base a (nxt w.C q) ≠ w.base a (nxt w.C l) := by rw [bnq, bnl]; exact d4
        rw [hx hqC hlC m1, hx (w.nxt_mem hqC) hlC m2, hx hqC (w.nxt_mem hlC) m3,
          hx (w.nxt_mem hqC) (w.nxt_mem hlC) m4, bq, bl, bnq, bnl]
        exact hrow

/-- **Lifting a flat-folded state through a crimp.**  Every flat-folded state of the crimped
walk lifts to one of the walk that agrees with it at every surviving crease and gives the
two deleted creases the layer value `t`. -/
theorem exists_lift {h' : ι → ℤ} (hf : (w.crimp a hc).IsFlat h') (t : Bool) :
    ∃ h, w.IsFlat h ∧
      (∀ k ∈ (w.crimp a hc).C, xOf h k (nxt w.C k) = xOf h' k (nxt (w.crimp a hc).C k)) ∧
      xOf h (prv w.C a) a = (if t then 1 else 0) ∧ xOf h a (nxt w.C a) = (if t then 1 else 0) := by
  refine ⟨w.liftH a h' t, ⟨hc.liftH_injOn hf.1 t, hc.liftH_isSol hf t⟩, ?_, hc.block_val h' t⟩
  intro k hk
  obtain ⟨hka, hkA, hkC⟩ := mem_crimpC.1 hk
  have bk : w.base a k = k := hc.base_of_out hkA hka
  have bnk := hc.base_nxt hkC hkA hka
  have hne : w.base a k ≠ w.base a (nxt w.C k) := by
    rw [bk, bnk]; exact ((w.crimp a hc).nxt_ne hk).symm
  rw [hc.xOf_liftH hf.1 t hkC (w.nxt_mem hkC) hne, bk, bnk]

end CrimpOK

/-! ### Every walk has a flat-folded state -/

/-- With two creases, every crease is one end of every sector. -/
lemma two_creases {q g : ι} (h2 : w.C.card = 2) (hq : q ∈ w.C) (hg : g ∈ w.C) :
    q = g ∨ q = prv w.C g := by
  by_contra h
  push_neg at h
  have hsub : ({g, prv w.C g, q} : Finset ι) ⊆ w.C := by
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
    · exact hg
    · exact w.prv_mem hg
    · exact hq
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [(w.prv_ne hg).symm, Ne.symm h.1]),
    Finset.card_pair (Ne.symm h.2)] at this
  omega

/-- A walk with two creases has no row. -/
lemma rows_eq_empty_of_two (h2 : w.C.card = 2) : w.rows = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro r hr
  rcases mem_rows.1 hr with hr | hr
  · obtain ⟨q, g, hqg, -⟩ := mem_ttRows.1 hr
    obtain ⟨d1, d2⟩ := tt_distinct hqg
    rcases two_creases h2 hqg.1 hqg.2.1 with e | e
    · exact d1 e
    · exact d2 (by rw [e, nxt_prv hqg.2.1])
  · obtain ⟨q, l, -, ⟨hq, hl, hne, hcq, -⟩, -⟩ := mem_tcRows.1 hr
    rcases two_creases h2 hq hl with e | e
    · exact hne e
    · exact c_prv_ne hl (e ▸ hcq)

lemma sum_nxt_two {x : ι → ι → ZMod 2} (h2 : w.C.card = 2) (hx : w.Antisymm x) :
    ∑ k ∈ w.C, x k (nxt w.C k) = 1 := by
  obtain ⟨k, hk⟩ := w.nonempty
  have hk' := w.nxt_mem hk
  have hne := (w.nxt_ne hk).symm
  have hC : w.C = {k, nxt w.C k} := by
    symm; apply Finset.eq_of_subset_of_card_le
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
    · rw [h2, Finset.card_pair hne]
  have hnn : nxt w.C (nxt w.C k) = k := by
    have hm : nxt w.C (nxt w.C k) ∈ ({k, nxt w.C k} : Finset ι) := by
      rw [← hC]; exact w.nxt_mem hk'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact h
    · exact absurd h (w.nxt_ne hk')
  calc ∑ i ∈ w.C, x i (nxt w.C i) = ∑ i ∈ ({k, nxt w.C k} : Finset ι), x i (nxt w.C i) := by
        rw [← hC]
    _ = x k (nxt w.C k) + x (nxt w.C k) k := by rw [Finset.sum_pair hne, hnn]
    _ = 1 := by
        rw [hx k hk _ hk' hne]; generalize x k (nxt w.C k) = u; revert u; decide

/-- **Every walk has a flat-folded state**, and it satisfies the vertex row.  By induction,
crimping a sector of smallest angle and lifting (`exists_lift`). -/
theorem exists_flat : ∀ (n : ℕ) (w : Walk ι α), w.C.card = n →
    ∃ h, w.IsFlat h ∧ ∑ k ∈ w.C, xOf h k (nxt w.C k) = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn
  by_cases h2 : w.C.card = 2
  · obtain ⟨k, hk⟩ := w.nonempty
    have hinj : Set.InjOn (fun i => if i = k then (0 : ℤ) else 1) w.C := by
      intro i hi j hj e
      by_cases hik : i = k <;> by_cases hjk : j = k
      · rw [hik, hjk]
      · simp only [hik, hjk, if_true, if_false] at e; exact absurd e (by norm_num)
      · simp only [hik, hjk, if_true, if_false] at e; exact absurd e (by norm_num)
      · rw [(two_creases h2 hi hk).resolve_left hik, (two_creases h2 hj hk).resolve_left hjk]
    refine ⟨fun i => if i = k then 0 else 1, ⟨hinj, ?_⟩, sum_nxt_two h2 (antisymm_xOf hinj)⟩
    intro r hr; rw [rows_eq_empty_of_two h2] at hr; simp at hr
  · have h4 : 4 ≤ w.C.card := by
      have := w.two_le; obtain ⟨m, hm⟩ := card_even (w := w); omega
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image w.C w.len w.nonempty
    have hc : w.CrimpOK a := ⟨ha, h4, hmin _ (w.prv_mem ha), hmin _ (w.nxt_mem ha)⟩
    obtain ⟨h', hf', hs'⟩ := ih (w.C.card - 2) (by omega) (w.crimp a hc) (card_crimpC hc)
    obtain ⟨h, hf, hagree, hv1, hv2⟩ := hc.exists_lift hf' false
    refine ⟨h, hf, ?_⟩
    rw [← Finset.add_sum_erase _ _ hc.memA,
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hc.A_ne_a.symm, ha⟩), nxt_prv ha, hv1, hv2]
    have : ∑ x ∈ (w.C.erase (prv w.C a)).erase a, xOf h x (nxt w.C x) =
        ∑ x ∈ (w.crimp a hc).C, xOf h' x (nxt (w.crimp a hc).C x) :=
      Finset.sum_congr rfl fun k hk => hagree k hk
    rw [this, hs']; simp

end Walk

end Origami