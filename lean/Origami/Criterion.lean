import Origami.Generic

/-!
# Corollary 2: where the linear constraints suffice

`|W_lin| = 2^(n-1-E)` is Theorem 4 (`card_Wlin`).  Corollary 2 compares it with Hull's count
of flat-foldable assignments: `W_lin = W_flat` iff every run crimped in the recursion is a
single sector and the recursion ends at degree two or four.

The direction proved here is the one that needs no count: if the recursion is *simple* (single
sectors, ending at degree two or four), then `W₄ ⊆ W_flat`, hence `W_lin = W_flat`.  The step
and the base of degree two are those of the generic case (`step_k0_flat`, `base_two_flat`);
the base of degree four, four equal angles, is checked on its eight flat states.  The converse
rests on Hull's enumeration of flat-foldable assignments, which the paper cites and which is
not formalized here.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-! ### Four equal angles, combinatorially -/

/-- The eight stackings of four equal sectors that fold flat: heights of the sectors
`0, 1, 2, 3`, in cyclic order, with maxima at the even creases. -/
def quadStates : List (Fin 4 → ℤ) :=
  [![1, 0, 3, 2], ![3, 0, 1, 2], ![3, 2, 1, 0], ![2, 1, 0, 3],
   ![1, 2, 3, 0], ![0, 1, 2, 3], ![0, 3, 2, 1], ![2, 3, 0, 1]]

/-- The assignment induced at the crease `i` (a maximum iff `i` is even). -/
def quadAsg (t : Fin 4 → ℤ) (i : Fin 4) : ZMod 2 :=
  (if t i < t (i + 1) then 1 else 0) + if i.val % 2 = 0 then 0 else 1

/-- `[t a < t b]` over `𝔽₂`. -/
def ltz (t : Fin 4 → ℤ) (a b : Fin 4) : ZMod 2 := if t a < t b then 1 else 0

lemma quad_inj : ∀ t ∈ quadStates, ∀ a b : Fin 4, t a = t b → a = b := by decide

/-- The eight stackings satisfy the two taco–taco rows. -/
lemma quad_rows : ∀ t ∈ quadStates, ∀ i j : Fin 4, i ≠ j → i.val % 2 = j.val % 2 →
    ltz t i j + ltz t (i + 1) j + ltz t i (j + 1) + ltz t (i + 1) (j + 1) = 0 := by decide

/-- They induce every assignment with an odd number of valleys. -/
lemma quad_cover : ∀ a : Fin 4 → ZMod 2, (Finset.univ.filter fun i => a i = 1).card % 2 = 1 →
    ∃ t ∈ quadStates, ∀ i, quadAsg t i = a i := by decide

namespace Walk

variable {w : Walk ι α}

/-- A walk with four equal angles: its creases `k 0, …, k 3` in cyclic order from a maximum,
the maxima on one ray and the minima on another, every sector spanning both. -/
lemma quad_of_four (hA : w.AllEq) (h4 : w.C.card = 4) :
    ∃ k : Fin 4 → ι, (∀ i, k i ∈ w.C) ∧ (∀ i, nxt w.C (k i) = k (i + 1)) ∧
      Function.Injective k ∧ w.C = Finset.univ.image k ∧
      (∀ i, w.up (k i) ↔ i.val % 2 = 0) ∧
      (∀ i, w.c (k i) = if i.val % 2 = 0 then w.c (k 0) else w.c (k 1)) ∧
      w.c (k 1) < w.c (k 0) ∧ (∀ g ∈ w.C, w.lo g = w.c (k 1) ∧ w.hi g = w.c (k 0)) := by
  obtain ⟨k0, hk0, hu0⟩ : ∃ k ∈ w.C, w.up k := by
    by_contra hne
    push_neg at hne
    have := card_not_up (w := w)
    rw [Finset.filter_true_of_mem (fun k hk => hne k hk)] at this
    omega
  set k : Fin 4 → ι := fun i => (nxt w.C)^[i.val] k0 with hkdef
  have mem : ∀ i, k i ∈ w.C := fun i => iterate_mem hk0 _
  have hnxt : ∀ i, nxt w.C (k i) = k (i + 1) := by
    intro i
    fin_cases i
    · exact (Function.iterate_succ_apply' _ _ _).symm
    · exact (Function.iterate_succ_apply' _ _ _).symm
    · exact (Function.iterate_succ_apply' _ _ _).symm
    · show nxt w.C ((nxt w.C)^[3] k0) = k0
      rw [← Function.iterate_succ_apply' (nxt w.C)]
      have := iterate_card hk0
      rw [h4] at this
      exact this
  have hinj : Function.Injective k := by
    intro i j h
    exact Fin.ext (iterate_inj hk0 (by rw [h4]; exact i.2) (by rw [h4]; exact j.2) h)
  have hC : w.C = Finset.univ.image k := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
      exact mem i
    · rw [Finset.card_image_of_injective _ hinj, h4]; rfl
  have hprv : ∀ i, prv w.C (k (i + 1)) = k i := fun i => by rw [← hnxt i, prv_nxt (mem i)]
  have hup : ∀ i, w.up (k i) ↔ i.val % 2 = 0 := by
    have s : ∀ i, w.up (k (i + 1)) ↔ ¬ w.up (k i) := fun i => by rw [← hnxt i]; exact up_nxt (mem i)
    have u0 : w.up (k 0) := hu0
    have u1 : ¬ w.up (k 1) := fun h => (s 0).1 h u0
    have u2 : w.up (k 2) := (s 1).2 u1
    have u3 : ¬ w.up (k 3) := fun h => (s 2).1 h u2
    intro i
    fin_cases i
    · exact iff_of_true u0 rfl
    · exact iff_of_false u1 (by decide)
    · exact iff_of_true u2 rfl
    · exact iff_of_false u3 (by decide)
  -- the four sectors have the same length
  have hlen : ∀ i, w.len (k i) = w.len (k 1) := fun i => hA _ (mem i) _ (mem 1)
  have p1 : prv w.C (k 1) = k 0 := hprv 0
  have p2 : prv w.C (k 2) = k 1 := hprv 1
  have p3 : prv w.C (k 3) = k 2 := hprv 2
  have p0 : prv w.C (k 0) = k 3 := hprv 3
  have l1 := lo_hi_of_not_up (mem 1) ((hup 1).not.2 (by decide))
  have l2 := lo_hi_of_up ((hup 2).2 rfl)
  have l3 := lo_hi_of_not_up (mem 3) ((hup 3).not.2 (by decide))
  have l0 := lo_hi_of_up ((hup 0).2 rfl)
  rw [p1] at l1; rw [p2] at l2; rw [p3] at l3; rw [p0] at l0
  have e2 := hlen 2; have e3 := hlen 3
  unfold len at e2 e3
  rw [l1.1, l1.2, l2.1, l2.2] at e2
  rw [l1.1, l1.2, l3.1, l3.2] at e3
  have c2 : w.c (k 2) = w.c (k 0) := by linarith
  have c3 : w.c (k 3) = w.c (k 1) := by linarith
  have c10 : w.c (k 1) < w.c (k 0) := by
    have := lo_lt_hi (mem 1); rw [l1.1, l1.2] at this; exact this
  refine ⟨k, mem, hnxt, hinj, hC, hup, ?_, c10, ?_⟩
  · intro i
    fin_cases i
    · rfl
    · rfl
    · exact c2
    · exact c3
  · intro g hg
    rw [hC] at hg
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hg
    fin_cases i
    · exact ⟨l0.1.trans c3, l0.2⟩
    · exact ⟨l1.1, l1.2⟩
    · exact ⟨l2.1, l2.2.trans c2⟩
    · exact ⟨l3.1.trans c3, l3.2.trans c2⟩

/-- **The base of degree four.**  At four equal angles, every assignment with
`M - V ≡ 2 (mod 4)` folds flat. -/
lemma base_four_flat (hA : w.AllEq) (h4 : w.C.card = 4) {σ : w.C → ZMod 2}
    (hσ : w.mv σ % 4 = 2) : σ ∈ w.Wflat := by
  obtain ⟨k, mem, hnxt, hinj, hC, hup, hc, c10, hlh⟩ := quad_of_four hA h4
  -- the number of valleys is odd
  set a : Fin 4 → ZMod 2 := fun i => σ ⟨k i, mem i⟩
  have hodd : (Finset.univ.filter fun i => a i = 1).card % 2 = 1 := by
    rw [mv_eq] at hσ
    have e : w.C.filter (fun j => w.ext0 σ j = 1) =
        (Finset.univ.filter fun i => a i = 1).image k := by
      rw [hC, Finset.filter_image]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
      rw [show w.ext0 σ (k i) = σ ⟨k i, mem i⟩ from ext0_mem σ ⟨k i, mem i⟩]
    rw [e, Finset.card_image_of_injective _ hinj, h4] at hσ
    omega
  obtain ⟨t, ht, hta⟩ := quad_cover a hodd
  -- the stacking `t`, as heights of the sectors
  set H : ι → ℤ := fun j => ∑ i, if k i = j then t i else 0
  have hH : ∀ i, H (k i) = t i := by
    intro i
    show (∑ i', if k i' = k i then t i' else 0) = t i
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg (fun e => hb (hinj e))]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hx : ∀ i j, xOf H (k i) (k j) = ltz t i j := fun i j => by
    simp only [xOf, ltz, hH]
  have memk : ∀ {q}, q ∈ w.C → ∃ i, q = k i := fun hq => by
    rw [hC] at hq; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq; exact ⟨i, rfl⟩
  have hpar : ∀ i j, w.c (k i) = w.c (k j) → i.val % 2 = j.val % 2 := by
    intro i j e
    rw [hc i, hc j] at e
    have h01 : w.c (k 1) ≠ w.c (k 0) := ne_of_lt c10
    have hi : i.val % 2 = 0 ∨ i.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
    have hj : j.val % 2 = 0 ∨ j.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> simp only [hi, hj] at e ⊢ <;>
      first | rfl | exact absurd e h01 | exact absurd e.symm h01
  have hflat : w.IsFlat H := by
    refine ⟨?_, fun r hr => ?_⟩
    · intro p hp q hq e
      obtain ⟨i, rfl⟩ := memk hp
      obtain ⟨j, rfl⟩ := memk hq
      rw [hH, hH] at e
      rw [quad_inj t ht i j e]
    · rcases mem_rows.1 hr with hr | hr
      · obtain ⟨q, g, ⟨hq, hg, h1, h2⟩, -⟩ := mem_ttRows.1 hr
        obtain ⟨i, rfl⟩ := memk hq
        rw [(hlh g hg).1] at h1; rw [(hlh g hg).2] at h2
        rw [hc i] at h1 h2
        split_ifs at h1 h2 <;>
          first | exact absurd h2 (lt_irrefl _) | exact absurd h1 (lt_irrefl _)
      · obtain ⟨q, l, -, ⟨hq, hl, hne, heq, -⟩, rfl⟩ := mem_tcRows.1 hr
        obtain ⟨i, rfl⟩ := memk hq
        obtain ⟨j, rfl⟩ := memk hl
        rw [Row.eval_tc, hnxt, hnxt, hx, hx, hx, hx]
        exact quad_rows t ht i j (fun e => hne (by rw [e])) (hpar i j heq)
  refine ⟨H, hflat, funext fun q => ?_⟩
  obtain ⟨i, hi⟩ := memk q.2
  have hq : q = ⟨k i, mem i⟩ := Subtype.ext hi
  subst hq
  rw [asg_xOf, hnxt, hx]
  show ltz t i (i + 1) + _ = a i
  rw [← hta i, quadAsg]
  by_cases h : i.val % 2 = 0
  · rw [if_pos ((hup i).2 h), if_pos h]; rfl
  · rw [if_neg (fun e => h ((hup i).1 e)), if_neg h]; rfl

/-! ### Simple recursions -/

/-- A run of Hull's recursion is *simple* if every crimped run is a single sector and it ends
at degree two or four. -/
def Chain.Simple : {w : Walk ι α} → Chain w → Prop
  | w, Chain.base _ => w.C.card = 2 ∨ w.C.card = 4
  | _, Chain.step R c => R.k = 0 ∧ c.Simple

/-- Along a simple recursion, Hull's conditions read modulo four are exact. -/
theorem W4_flat_simple : ∀ {w : Walk ι α} (c : Chain w), c.Simple → c.W4 ⊆ w.Wflat := by
  intro w c
  induction c with
  | @base w h =>
    rintro (h2 | h4) σ hσ
    · exact base_two_flat h2 hσ
    · exact base_four_flat h h4 hσ
  | @step w R c ih => exact fun hs => step_k0_flat R hs.1 c (ih hs.2)

/-- **Corollary 2 (where the linear constraints suffice), proved direction.**  For every run of
Hull's recursion, `|W_lin| = 2^(n-1-E)`; if every crimped run is a single sector and the
recursion ends at degree two or four, then `W_lin = W_flat`; in particular `W_lin = W_flat`
at every vertex without taco–taco rows. -/
theorem corollary2 (c : Chain w) :
    w.Wlin.ncard = 2 ^ (w.C.card - 1 - c.E) ∧ (c.Simple → w.Wlin = w.Wflat) ∧
      (w.NoTC → w.Wlin = w.Wflat) :=
  ⟨(card_Wlin c).1,
    fun hs => subset_antisymm ((theorem3 c).1 ▸ W4_flat_simple c hs) Wflat_subset_Wlin,
    fun hn => subset_antisymm ((theorem3 c).1 ▸ W4_flat_generic c hn) Wflat_subset_Wlin⟩

end Walk

end Origami
