import Origami.Cyclic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Closed walks, their rows, layer variables and flat-folded states

This file sets up Sections 2 and 3 of the paper in the one-dimensional model.

* A **closed walk** (`Walk`) is a finite set `C` of creases, read cyclically, with a
  position `c k` for every crease, such that every crease is a strict local maximum or a
  strict local minimum of the cyclic sequence of positions.  The sector `g ∈ C` is the
  one that *ends* at the crease `g`: it lies between the creases `prv C g` and `g`, and
  its folded image is the interval `[lo g, hi g]` (Eq. (4) of the paper).  The two sectors
  at the crease `k` are `k` and `nxt C k`.
* By Lemma 1 of the paper, the taco–tortilla and taco–taco rows at a vertex depend only on
  its walk; we *define* them from the walk (`IsTT`, `IsTC`), exactly as stated in Lemma 1.
* **Layer variables** are functions `x : ι → ι → ZMod 2`, antisymmetric on `C`
  (`x j i = x i j + 1`): `x i j = 0` means that `f_i` lies above `f_j`.
* A **flat-folded state** is a height function `h : ι → ℤ`, injective on `C`, whose
  layer variables `xOf h` satisfy every row.  Transitivity is built in, since the layers
  are totally ordered by their heights.
* The **mountain–valley assignment** induced by layer variables is
  `asg x k = x k (nxt k) + [k is a minimum]` (Eq. (1), `σ = p r`, written over `𝔽₂`).
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- A closed walk with positive steps: every crease is a strict local extremum. -/
structure Walk (ι α : Type*) [LinearOrder ι] [LinearOrder α] where
  /-- the creases -/
  C : Finset ι
  /-- the position of every crease in the folded image -/
  c : ι → α
  two_le : 2 ≤ C.card
  zig : ∀ k ∈ C, (c (prv C k) < c k ∧ c (nxt C k) < c k) ∨
    (c k < c (prv C k) ∧ c k < c (nxt C k))

/-- A row: a taco–tortilla row `tt k k' g` (taco `f_k, f_k'` folded at the crease `k`,
`k' = nxt k`, tortilla `f_g`) or a taco–taco row `tc k k' l l'`. -/
inductive Row (ι : Type*)
  | tt (k k' g : ι)
  | tc (k k' l l' : ι)
  deriving DecidableEq

namespace Row

/-- The oriented pairs of sectors whose layer variables appear in the row. -/
def terms : Row ι → List (ι × ι)
  | tt k k' g => [(k, g), (k', g)]
  | tc k k' l l' => [(k, l), (k', l), (k, l'), (k', l')]

/-- The left-hand side of the row; the row is the equation `eval r x = 0`. -/
def eval (r : Row ι) (x : ι → ι → ZMod 2) : ZMod 2 :=
  (r.terms.map fun t => x t.1 t.2).sum

/-- The vertices of the row in the hypergraph `H_v`: unordered pairs of sectors. -/
def verts (r : Row ι) : Finset (Sym2 ι) :=
  (r.terms.map fun t => s(t.1, t.2)).toFinset

lemma eval_add (r : Row ι) (x y : ι → ι → ZMod 2) :
    r.eval (x + y) = r.eval x + r.eval y := by
  cases r <;> simp [eval, terms] <;> ring

@[simp] lemma eval_tt (k k' g : ι) (x : ι → ι → ZMod 2) :
    (tt k k' g).eval x = x k g + x k' g := by simp [eval, terms]

@[simp] lemma eval_tc (k k' l l' : ι) (x : ι → ι → ZMod 2) :
    (tc k k' l l').eval x = x k l + x k' l + x k l' + x k' l' := by simp [eval, terms]; ring

end Row

namespace Walk

variable (w : Walk ι α)

lemma nonempty : w.C.Nonempty := Finset.card_pos.1 (by have := w.two_le; omega)

lemma nxt_mem {k : ι} (_hk : k ∈ w.C) : nxt w.C k ∈ w.C := Origami.nxt_mem w.nonempty k
lemma prv_mem {k : ι} (_hk : k ∈ w.C) : prv w.C k ∈ w.C := Origami.prv_mem w.nonempty k

lemma nxt_ne {k : ι} (hk : k ∈ w.C) : nxt w.C k ≠ k := Origami.nxt_ne hk w.two_le
lemma prv_ne {k : ι} (hk : k ∈ w.C) : prv w.C k ≠ k := Origami.prv_ne hk w.two_le

/-- The crease `k` is a local maximum of the walk (the sector `k` goes up). -/
def up (k : ι) : Prop := w.c (prv w.C k) < w.c k

instance : DecidablePred w.up := fun k => by unfold up; infer_instance

variable {w}

lemma up_iff_nxt {k : ι} (hk : k ∈ w.C) : w.up k ↔ w.c (nxt w.C k) < w.c k := by
  unfold up
  rcases w.zig k hk with h | h
  · simp [h.1, h.2]
  · simp [not_lt.2 h.1.le, not_lt.2 h.2.le]

lemma not_up_iff {k : ι} (hk : k ∈ w.C) : ¬ w.up k ↔ w.c k < w.c (prv w.C k) := by
  unfold up
  rcases w.zig k hk with h | h
  · simp [h.1, not_lt.2 h.1.le]
  · simp [h.1, not_lt.2 h.1.le]

lemma not_up_iff_nxt {k : ι} (hk : k ∈ w.C) : ¬ w.up k ↔ w.c k < w.c (nxt w.C k) := by
  rw [not_up_iff hk]
  rcases w.zig k hk with h | h
  · simp [not_lt.2 h.1.le, not_lt.2 h.2.le]
  · simp [h.1, h.2]

lemma c_prv_ne {k : ι} (hk : k ∈ w.C) : w.c (prv w.C k) ≠ w.c k := by
  rcases w.zig k hk with h | h
  · exact ne_of_lt h.1
  · exact ne_of_gt h.1

lemma c_nxt_ne {k : ι} (hk : k ∈ w.C) : w.c (nxt w.C k) ≠ w.c k := by
  rcases w.zig k hk with h | h
  · exact ne_of_lt h.2
  · exact ne_of_gt h.2

lemma up_nxt {k : ι} (hk : k ∈ w.C) : w.up (nxt w.C k) ↔ ¬ w.up k := by
  unfold up
  rw [prv_nxt hk, ← not_up_iff_nxt hk]
  rfl

lemma up_prv {k : ι} (hk : k ∈ w.C) : w.up (prv w.C k) ↔ ¬ w.up k := by
  have := up_nxt (w.prv_mem hk)
  rw [nxt_prv hk] at this
  tauto

/-! ### Sectors and their intervals -/

variable (w)

/-- Lower end of the interval of the sector `g` (which ends at the crease `g`). -/
def lo (g : ι) : α := min (w.c (prv w.C g)) (w.c g)
/-- Upper end of the interval of the sector `g`. -/
def hi (g : ι) : α := max (w.c (prv w.C g)) (w.c g)
/-- The angle of the sector `g`. -/
def len (g : ι) : α := w.hi g - w.lo g

/-- Two sectors overlap: their intervals meet in more than a point. -/
def Overlap (a b : ι) : Prop := max (w.lo a) (w.lo b) < min (w.hi a) (w.hi b)

instance (a b : ι) : Decidable (w.Overlap a b) := by unfold Overlap; infer_instance

/-- Lower crease of the sector `g` (a local minimum). -/
def lc (g : ι) : ι := if w.up g then prv w.C g else g
/-- Upper crease of the sector `g` (a local maximum). -/
def uc (g : ι) : ι := if w.up g then g else prv w.C g

variable {w}

lemma lo_hi_of_up {g : ι} (h : w.up g) :
    w.lo g = w.c (prv w.C g) ∧ w.hi g = w.c g := by
  unfold lo hi; unfold up at h
  exact ⟨min_eq_left h.le, max_eq_right h.le⟩

lemma lo_hi_of_not_up {g : ι} (hg : g ∈ w.C) (h : ¬ w.up g) :
    w.lo g = w.c g ∧ w.hi g = w.c (prv w.C g) := by
  rw [not_up_iff hg] at h
  unfold lo hi
  exact ⟨min_eq_right h.le, max_eq_left h.le⟩

lemma lo_lt_hi {g : ι} (hg : g ∈ w.C) : w.lo g < w.hi g := by
  by_cases h : w.up g
  · rw [(lo_hi_of_up h).1, (lo_hi_of_up h).2]; exact h
  · rw [(lo_hi_of_not_up hg h).1, (lo_hi_of_not_up hg h).2]; exact (not_up_iff hg).1 h

lemma len_pos {g : ι} (hg : g ∈ w.C) : 0 < w.len g := by
  unfold len; linarith [lo_lt_hi hg]

lemma c_lc {g : ι} (hg : g ∈ w.C) : w.c (w.lc g) = w.lo g := by
  unfold lc; split_ifs with h
  · exact (lo_hi_of_up h).1.symm
  · exact (lo_hi_of_not_up hg h).1.symm

lemma c_uc {g : ι} (hg : g ∈ w.C) : w.c (w.uc g) = w.hi g := by
  unfold uc; split_ifs with h
  · exact (lo_hi_of_up h).2.symm
  · exact (lo_hi_of_not_up hg h).2.symm

lemma lc_mem {g : ι} (hg : g ∈ w.C) : w.lc g ∈ w.C := by
  unfold lc; split_ifs <;> [exact w.prv_mem hg; exact hg]

lemma uc_mem {g : ι} (hg : g ∈ w.C) : w.uc g ∈ w.C := by
  unfold uc; split_ifs <;> [exact hg; exact w.prv_mem hg]

lemma not_up_lc {g : ι} (hg : g ∈ w.C) : ¬ w.up (w.lc g) := by
  unfold lc; split_ifs with h
  · rw [up_prv hg]; exact not_not.2 h
  · exact h

lemma up_uc {g : ι} (hg : g ∈ w.C) : w.up (w.uc g) := by
  unfold uc; split_ifs with h
  · exact h
  · rw [up_prv hg]; exact h

lemma lc_ne_uc {g : ι} (hg : g ∈ w.C) : w.lc g ≠ w.uc g := fun h =>
  not_up_lc hg (h ▸ up_uc hg)

/-- The creases of the sector `g` are `prv g` and `g`; the crease `q` is one of them iff
`g` is one of the two sectors `q, nxt q` at `q`. -/
lemma sector_at_iff {g q : ι} (hg : g ∈ w.C) (hq : q ∈ w.C) :
    (g = q ∨ g = nxt w.C q) ↔ (q = g ∨ q = prv w.C g) := by
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (prv_nxt hq).symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (nxt_prv hg).symm

/-- A crease of `g` that is a maximum is its upper crease. -/
lemma eq_uc_of_up {g q : ι} (hg : g ∈ w.C) (hq : q = g ∨ q = prv w.C g) (h : w.up q) :
    q = w.uc g := by
  unfold uc
  rcases hq with rfl | rfl
  · simp [h]
  · rw [up_prv hg] at h; simp [h]

/-- A crease of `g` that is a minimum is its lower crease. -/
lemma eq_lc_of_not_up {g q : ι} (hg : g ∈ w.C) (hq : q = g ∨ q = prv w.C g) (h : ¬ w.up q) :
    q = w.lc g := by
  unfold lc
  rcases hq with rfl | rfl
  · simp [h]
  · rw [up_prv hg] at h; simp at h; simp [h]

/-! ### Rows (Lemma 1 of the paper, taken as the definition) -/

variable (w)

/-- Taco–tortilla: the crease `q` lies in the interior of the interval of the sector `g`. -/
def IsTT (q g : ι) : Prop := q ∈ w.C ∧ g ∈ w.C ∧ w.lo g < w.c q ∧ w.c q < w.hi g

/-- Taco–taco: two distinct creases on the same ray, both maxima or both minima. -/
def IsTC (q l : ι) : Prop :=
  q ∈ w.C ∧ l ∈ w.C ∧ q ≠ l ∧ w.c q = w.c l ∧ (w.up q ↔ w.up l)

/-- The taco–tortilla rows at the vertex. -/
def ttRows : Finset (Row ι) :=
  ((w.C ×ˢ w.C).filter fun p => w.lo p.2 < w.c p.1 ∧ w.c p.1 < w.hi p.2).image
    fun p => Row.tt p.1 (nxt w.C p.1) p.2

/-- The taco–taco rows at the vertex (each unordered pair of creases once). -/
def tcRows : Finset (Row ι) :=
  ((w.C ×ˢ w.C).filter fun p => p.1 < p.2 ∧ w.c p.1 = w.c p.2 ∧ (w.up p.1 ↔ w.up p.2)).image
    fun p => Row.tc p.1 (nxt w.C p.1) p.2 (nxt w.C p.2)

/-- All the rows at the vertex. -/
def rows : Finset (Row ι) := w.ttRows ∪ w.tcRows

variable {w}

lemma mem_ttRows {r : Row ι} :
    r ∈ w.ttRows ↔ ∃ q g, w.IsTT q g ∧ r = Row.tt q (nxt w.C q) g := by
  unfold ttRows IsTT
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨q, g, ⟨⟨hq, hg⟩, h1, h2⟩, rfl⟩; exact ⟨q, g, ⟨hq, hg, h1, h2⟩, rfl⟩
  · rintro ⟨q, g, ⟨hq, hg, h1, h2⟩, rfl⟩; exact ⟨q, g, ⟨⟨hq, hg⟩, h1, h2⟩, rfl⟩

lemma mem_tcRows {r : Row ι} :
    r ∈ w.tcRows ↔ ∃ q l, q < l ∧ w.IsTC q l ∧ r = Row.tc q (nxt w.C q) l (nxt w.C l) := by
  unfold tcRows IsTC
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨q, l, ⟨⟨hq, hl⟩, h1, h2, h3⟩, rfl⟩
    exact ⟨q, l, h1, ⟨hq, hl, ne_of_lt h1, h2, h3⟩, rfl⟩
  · rintro ⟨q, l, h1, ⟨hq, hl, -, h2, h3⟩, rfl⟩; exact ⟨q, l, ⟨⟨hq, hl⟩, h1, h2, h3⟩, rfl⟩

lemma mem_rows {r : Row ι} : r ∈ w.rows ↔ r ∈ w.ttRows ∨ r ∈ w.tcRows := Finset.mem_union

/-- A walk is generic if no two creases lie on the same ray. -/
def Generic (w : Walk ι α) : Prop := Set.InjOn w.c w.C

lemma tcRows_eq_empty_of_generic (hg : w.Generic) : w.tcRows = ∅ := by
  ext r
  simp only [Finset.notMem_empty, iff_false]
  intro hr
  obtain ⟨q, l, -, ⟨hq, hl, hne, heq, -⟩, -⟩ := mem_tcRows.1 hr
  exact hne (hg hq hl heq)

/-! ### Layer variables, solutions, assignments and flat-folded states -/

variable (w)

/-- Layer variables are antisymmetric on the sectors: `x_{ji} = x_{ij} + 1`. -/
def Antisymm (x : ι → ι → ZMod 2) : Prop := ∀ i ∈ w.C, ∀ j ∈ w.C, i ≠ j → x j i = x i j + 1

/-- The layer variables satisfy every row at the vertex. -/
def IsSol (x : ι → ι → ZMod 2) : Prop := ∀ r ∈ w.rows, r.eval x = 0

/-- The mountain–valley assignment induced by the layer variables, `σ = p r` over `𝔽₂`.
The value `1` is a mountain at a minimum crease or a valley at a maximum one with
`x = 0`; only the alternation of the colour `p` matters for every statement. -/
def asg (x : ι → ι → ZMod 2) : w.C → ZMod 2 :=
  fun k => x k (nxt w.C k) + if w.up k then 0 else 1

/-- The layer variables of a stacking given by heights: `x i j = 1` iff `f_i` lies below
`f_j`. -/
def xOf (h : ι → ℤ) : ι → ι → ZMod 2 := fun i j => if h i < h j then 1 else 0

/-- A flat-folded state of the vertex: a stacking of its sectors (heights injective on
`C`) that satisfies every row; transitivity holds because heights are totally ordered. -/
def IsFlat (h : ι → ℤ) : Prop := Set.InjOn h w.C ∧ w.IsSol (xOf h)

/-- `W_lin`: the assignments induced by the solutions of the rows. -/
def Wlin : Set (w.C → ZMod 2) := {σ | ∃ x, w.Antisymm x ∧ w.IsSol x ∧ w.asg x = σ}

/-- `W_flat`: the flat-foldable assignments. -/
def Wflat : Set (w.C → ZMod 2) := {σ | ∃ h, w.IsFlat h ∧ w.asg (xOf h) = σ}

/-- Number of valleys (creases with value `1`). -/
def nV (σ : w.C → ZMod 2) : ℕ := (Finset.univ.filter fun k => σ k = 1).card

variable {w}

lemma antisymm_xOf {h : ι → ℤ} (hh : Set.InjOn h w.C) : w.Antisymm (xOf h) := by
  intro i hi j hj hij
  unfold xOf
  have : h i ≠ h j := fun e => hij (hh hi hj e)
  rcases lt_or_gt_of_ne this with h1 | h1
  · simp [h1, not_lt.2 h1.le]; decide
  · simp [h1, not_lt.2 h1.le]

lemma Wflat_subset_Wlin : w.Wflat ⊆ w.Wlin := by
  rintro σ ⟨h, ⟨hinj, hsol⟩, rfl⟩
  exact ⟨xOf h, antisymm_xOf hinj, hsol, rfl⟩

end Walk

end Origami
