import Origami.Generic

/-!
# Proposition 2: the rank of the rows at a generic vertex

The variables of the rows are the overlapping pairs of distinct sectors (`ovPairs`, `N` of
them); a function `y` on them gives layer variables `lay y` by reading the bit of `{a, b}` as
`x_{ab}` when `a < b` and as `x_{ba} + 1` when `b < a`, and every antisymmetric `x` is of this
form on the overlapping pairs (`res`).  At a vertex without taco–taco rows (in particular at a
generic vertex) every row has two variables, so the rows are the edges of a graph `R_v` on the
overlapping pairs, whose components are the classes of `Conn`.  Then (Proposition 2)

* the kernel of the rows is the space of functions constant on components, so the rows have
  rank `N - m - c`, where `m = γ` is the number of components with adjacent pairs (half the
  degree, Theorem 2) and `c` the number of the others;
* the solutions form a coset of the kernel: `2^(m + c)` of them;
* every assignment in `W_lin = W_flat` is induced by exactly `2^c` solutions.

By Lemma 2 an adjacent pair lies in one row and every other pair of a component without
adjacent pairs in two (`card_rowsWith_cyc`): the components with adjacent pairs are paths and
the others are cycles, as in the paper.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

lemma Row.eval_smul (r : Row ι) (c : ZMod 2) (x : ι → ι → ZMod 2) :
    r.eval (c • x) = c * r.eval x := by
  cases r <;> simp [Row.eval, Row.terms] <;> ring

lemma natCard_eq_two_pow (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

namespace Walk

variable {w : Walk ι α}

/-! ### The variables -/

/-- Overlap, read on unordered pairs. -/
def ovS (w : Walk ι α) : Sym2 ι → Prop :=
  Sym2.lift ⟨fun a b => w.Overlap a b, fun _ _ => propext overlap_comm⟩

/-- The overlapping pairs of distinct sectors: the vertices of `R_v`, `N` of them. -/
noncomputable def ovPairs (w : Walk ι α) : Finset (Sym2 ι) :=
  w.C.sym2.filter fun u => ¬ u.IsDiag ∧ w.ovS u

lemma mk_mem_ovPairs {a b : ι} :
    s(a, b) ∈ w.ovPairs ↔ a ∈ w.C ∧ b ∈ w.C ∧ a ≠ b ∧ w.Overlap a b := by
  simp only [ovPairs, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff, ovS,
    Sym2.lift_mk]
  tauto

lemma adj_mem_ovPairs {k : ι} (hk : k ∈ w.C) : w.adj k ∈ w.ovPairs :=
  mk_mem_ovPairs.2 ⟨hk, w.nxt_mem hk, (w.nxt_ne hk).symm, overlap_nxt hk⟩

/-- The space of variables: one bit per overlapping pair. -/
abbrev Var (w : Walk ι α) := {u // u ∈ w.ovPairs}

/-- A function on the variables, extended by zero to all pairs. -/
noncomputable def hat (y : w.Var → ZMod 2) (u : Sym2 ι) : ZMod 2 :=
  if h : u ∈ w.ovPairs then y ⟨u, h⟩ else 0

lemma hat_add (y y' : w.Var → ZMod 2) (u : Sym2 ι) : hat (y + y') u = hat y u + hat y' u := by
  unfold hat; split_ifs <;> simp

lemma hat_smul (c : ZMod 2) (y : w.Var → ZMod 2) (u : Sym2 ι) : hat (c • y) u = c * hat y u := by
  unfold hat; split_ifs <;> simp

/-- The symmetric part of the layer variables of `y`. -/
noncomputable def lin (y : w.Var → ZMod 2) : ι → ι → ZMod 2 := fun a b => hat y s(a, b)

/-- The orientation: the bit of `{a, b}` is `x_{ab}` if `a < b`, and `x_{ab} + 1` if not. -/
def ori : ι → ι → ZMod 2 := fun a b => if b < a then 1 else 0

/-- The layer variables of `y`. -/
noncomputable def lay (y : w.Var → ZMod 2) : ι → ι → ZMod 2 := lin y + ori

/-- The restriction of layer variables to the overlapping pairs. -/
noncomputable def res (w : Walk ι α) (x : ι → ι → ZMod 2) : w.Var → ZMod 2 := fun u => symm2 x u.1

lemma lay_apply (y : w.Var → ZMod 2) (a b : ι) :
    lay y a b = hat y s(a, b) + if b < a then 1 else 0 := rfl

lemma antisymm_lay (y : w.Var → ZMod 2) : w.Antisymm (lay y) := by
  intro i _ j _ hij
  rw [lay_apply, lay_apply, Sym2.eq_swap]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [if_pos h, if_neg (not_lt.2 h.le)]; ring
  · rw [if_neg (not_lt.2 h.le), if_pos h]
    generalize hat y s(i, j) = u; revert u; decide

lemma lay_res {x : ι → ι → ZMod 2} (hx : w.Antisymm x) {a b : ι} (h : s(a, b) ∈ w.ovPairs) :
    lay (w.res x) a b = x a b := by
  obtain ⟨ha, hb, hab, -⟩ := mk_mem_ovPairs.1 h
  rw [lay_apply]
  unfold hat res
  rw [dif_pos h, symm2_mk]
  rcases lt_or_gt_of_ne hab with h1 | h1
  · rw [min_eq_left h1.le, max_eq_right h1.le, if_neg (not_lt.2 h1.le), add_zero]
  · rw [min_eq_right h1.le, max_eq_left h1.le, if_pos h1, hx b hb a ha (Ne.symm hab)]

/-- The pairs of a row are overlapping pairs of distinct sectors. -/
lemma mem_ovPairs_of_verts {r : Row ι} (hr : r ∈ w.rows) {u : Sym2 ι} (hu : u ∈ r.verts) :
    u ∈ w.ovPairs := by
  induction u using Sym2.ind with
  | _ a b =>
  have hs := Finset.mk_mem_sym2_iff.1 (verts_subset_sym2 hr hu)
  refine mk_mem_ovPairs.2 ⟨hs.1, hs.2, fun e => ?_, overlap_of_mem_verts hr hu⟩
  subst e; exact diag_not_mem_verts hr a hu

/-- The rows only see the overlapping pairs. -/
lemma eval_congr {x x' : ι → ι → ZMod 2} (h : ∀ a b, s(a, b) ∈ w.ovPairs → x a b = x' a b)
    {r : Row ι} (hr : r ∈ w.rows) : r.eval x = r.eval x' := by
  have hv : ∀ a b, s(a, b) ∈ r.verts → x a b = x' a b := fun a b hab =>
    h a b (mem_ovPairs_of_verts hr hab)
  rcases mem_rows.1 hr with hr' | hr'
  · obtain ⟨q, g, -, rfl⟩ := mem_ttRows.1 hr'
    simp only [Row.eval_tt]
    rw [hv q g (Row.mem_verts_tt.2 (Or.inl rfl)), hv _ g (Row.mem_verts_tt.2 (Or.inr rfl))]
  · obtain ⟨q, l, -, -, rfl⟩ := mem_tcRows.1 hr'
    simp only [Row.eval_tc]
    rw [hv q l (Row.mem_verts_tc.2 (Or.inl rfl)),
      hv _ l (Row.mem_verts_tc.2 (Or.inr (Or.inl rfl))),
      hv q _ (Row.mem_verts_tc.2 (Or.inr (Or.inr (Or.inl rfl)))),
      hv _ _ (Row.mem_verts_tc.2 (Or.inr (Or.inr (Or.inr rfl))))]

/-! ### The rows as a linear map and their kernel -/

/-- The linear parts of the rows, as a linear map on the variables. -/
noncomputable def rowMap (w : Walk ι α) : (w.Var → ZMod 2) →ₗ[ZMod 2] (w.rows → ZMod 2) where
  toFun y := fun r => r.1.eval (lin y)
  map_add' y y' := by
    funext r
    simp only [Pi.add_apply]
    rw [show lin (y + y') = lin y + lin y' from funext fun a => funext fun b => hat_add y y' _,
      Row.eval_add]
  map_smul' c y := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show lin (c • y) = c • lin y from funext fun a => funext fun b => hat_smul c y _,
      Row.eval_smul]

lemma rowMap_apply (y : w.Var → ZMod 2) (r : w.rows) : w.rowMap y r = r.1.eval (lin y) := rfl

lemma rows_tt (hn : w.NoTC) {r : Row ι} (hr : r ∈ w.rows) :
    ∃ q g, w.IsTT q g ∧ r = Row.tt q (nxt w.C q) g := by
  rcases mem_rows.1 hr with h | h
  · exact mem_ttRows.1 h
  · rw [tcRows_eq_empty_of_noTC hn] at h; simp at h

/-- **The kernel of the rows.**  Without taco–taco rows, `y` solves the homogeneous rows iff it
takes the same value on the two pairs of every row. -/
lemma mem_ker_iff (hn : w.NoTC) (y : w.Var → ZMod 2) :
    y ∈ LinearMap.ker w.rowMap ↔ ∀ u v, w.Linked u v → hat y u = hat y v := by
  rw [LinearMap.mem_ker]
  constructor
  · rintro h u v ⟨r, hr, hu, hv⟩
    have h0 := congrFun h ⟨r, hr⟩
    obtain ⟨q, g, -, rfl⟩ := rows_tt hn hr
    rw [rowMap_apply, Pi.zero_apply, Row.eval_tt] at h0
    have he : hat y s(q, g) = hat y s(nxt w.C q, g) := by
      change hat y s(q, g) + hat y s(nxt w.C q, g) = 0 at h0
      generalize hat y s(q, g) = A at h0 ⊢; generalize hat y s(nxt w.C q, g) = B at h0 ⊢
      revert A B; decide
    rw [Row.mem_verts_tt] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    all_goals first | rfl | exact he | exact he.symm
  · intro h
    funext ⟨r, hr⟩
    obtain ⟨q, g, -, rfl⟩ := rows_tt hn hr
    rw [rowMap_apply, Pi.zero_apply, Row.eval_tt]
    change hat y s(q, g) + hat y s(nxt w.C q, g) = 0
    rw [h s(q, g) s(nxt w.C q, g)
      ⟨_, hr, Row.mem_verts_tt.2 (Or.inl rfl), Row.mem_verts_tt.2 (Or.inr rfl)⟩]
    generalize hat y s(nxt w.C q, g) = A; revert A; decide

lemma hat_conn (hn : w.NoTC) {y : w.Var → ZMod 2} (hy : y ∈ LinearMap.ker w.rowMap)
    {u v : Sym2 ι} (h : w.Conn u v) : hat y u = hat y v := by
  have hl := (mem_ker_iff hn y).1 hy
  induction h with
  | rel a b h => exact hl a b h
  | refl => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

lemma ovPairs_conn {u v : Sym2 ι} (h : w.Conn u v) : u ∈ w.ovPairs ↔ v ∈ w.ovPairs := by
  induction h with
  | rel a b h =>
    obtain ⟨r, hr, ha, hb⟩ := h
    exact iff_of_true (mem_ovPairs_of_verts hr ha) (mem_ovPairs_of_verts hr hb)
  | refl => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Components -/

/-- The components of `R_v`. -/
noncomputable def comps (w : Walk ι α) : Finset (Quot w.Linked) := w.ovPairs.image (Quot.mk _)

/-- The components containing adjacent pairs; `γ` is their number. -/
noncomputable def adjComps (w : Walk ι α) : Finset (Quot w.Linked) :=
  w.C.image fun k => Quot.mk w.Linked (w.adj k)

/-- `c`: the number of components without adjacent pairs (the cycles of `R_v`). -/
noncomputable def cyc (w : Walk ι α) : ℕ := (w.comps \ w.adjComps).card

lemma gamma_eq : w.gamma = w.adjComps.card := by
  unfold gamma adjComps; congr

lemma adjComps_subset : w.adjComps ⊆ w.comps := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hq
  exact Finset.mem_image_of_mem _ (adj_mem_ovPairs hk)

lemma card_comps : w.comps.card = w.gamma + w.cyc := by
  rw [cyc, Finset.card_sdiff_of_subset adjComps_subset, gamma_eq]
  have := Finset.card_le_card (adjComps_subset (w := w))
  omega

/-- In a component without adjacent pairs, every pair lies in exactly two rows. -/
lemma card_rowsWith_cyc (h3 : 3 ≤ w.C.card) {u : Sym2 ι} (hu : u ∈ w.ovPairs)
    (hq : Quot.mk w.Linked u ∉ w.adjComps) : (w.rowsWith u).card = 2 := by
  induction u using Sym2.ind with
  | _ a b =>
  obtain ⟨ha, hb, hab, hov⟩ := mk_mem_ovPairs.1 hu
  rw [card_rowsWith ha hb hab h3, if_pos hov, if_neg]
  rintro (e | e)
  · exact hq (Finset.mem_image.2 ⟨a, ha, by rw [e]; rfl⟩)
  · exact hq (Finset.mem_image.2 ⟨b, hb, by rw [e, Sym2.eq_swap]; rfl⟩)

lemma out_mem {q : Quot w.Linked} (hq : q ∈ w.comps) : Quot.out q ∈ w.ovPairs := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hq
  exact (ovPairs_conn (Quot.eqvGen_exact (Quot.out_eq (Quot.mk w.Linked u)))).2 hu

/-- The kernel of the rows is the space of functions on the components. -/
noncomputable def kerEquiv (hn : w.NoTC) : LinearMap.ker w.rowMap ≃ (w.comps → ZMod 2) where
  toFun y := fun q => hat y.1 (Quot.out q.1)
  invFun g := ⟨fun u => g ⟨Quot.mk _ u.1, Finset.mem_image_of_mem _ u.2⟩, by
    rw [mem_ker_iff hn]
    rintro u v ⟨r, hr, hu, hv⟩
    unfold hat
    rw [dif_pos (mem_ovPairs_of_verts hr hu), dif_pos (mem_ovPairs_of_verts hr hv)]
    have e : (⟨Quot.mk w.Linked u, Finset.mem_image_of_mem _ (mem_ovPairs_of_verts hr hu)⟩ :
        w.comps) = ⟨Quot.mk w.Linked v, Finset.mem_image_of_mem _ (mem_ovPairs_of_verts hr hv)⟩ :=
      Subtype.ext (Quot.sound (show w.Linked u v from ⟨r, hr, hu, hv⟩))
    exact congrArg g e⟩
  left_inv y := by
    apply Subtype.ext
    funext u
    show hat y.1 (Quot.out (Quot.mk w.Linked u.1)) = y.1 u
    rw [hat_conn hn y.2 (Quot.eqvGen_exact (Quot.out_eq (Quot.mk w.Linked u.1)))]
    unfold hat; rw [dif_pos u.2]
  right_inv g := by
    funext q
    show hat _ (Quot.out q.1) = g q
    rw [hat, dif_pos (out_mem q.2)]
    have e : (⟨Quot.mk w.Linked (Quot.out q.1), Finset.mem_image_of_mem _ (out_mem q.2)⟩ :
        w.comps) = q := Subtype.ext (Quot.out_eq q.1)
    exact congrArg g e

lemma finrank_ker (hn : w.NoTC) :
    Module.finrank (ZMod 2) (LinearMap.ker w.rowMap) = w.comps.card := by
  have h : Nat.card (LinearMap.ker w.rowMap) = 2 ^ w.comps.card := by
    rw [Nat.card_congr (kerEquiv hn), Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2),
      ZMod.card, Nat.card_eq_fintype_card (α := w.comps), Fintype.card_coe]
  rw [natCard_eq_two_pow] at h
  exact Nat.pow_right_injective le_rfl h

/-! ### Solutions and assignments -/

/-- The solutions of the rows, as functions on the overlapping pairs. -/
def Sol (w : Walk ι α) : Set (w.Var → ZMod 2) := {y | w.IsSol (lay y)}

lemma mem_Sol_iff (y : w.Var → ZMod 2) :
    y ∈ w.Sol ↔ ∀ r : w.rows, w.rowMap y r = r.1.eval ori := by
  constructor
  · intro h r
    have := h r.1 r.2
    rw [lay, Row.eval_add] at this
    rw [rowMap_apply]
    generalize r.1.eval (lin y) = A at this ⊢; generalize r.1.eval ori = B at this ⊢
    revert A B; decide
  · intro h r hr
    have := h ⟨r, hr⟩
    rw [rowMap_apply] at this
    rw [lay, Row.eval_add, this]
    exact zmod2_add_self _

lemma res_mem_Sol {x : ι → ι → ZMod 2} (hx : w.Antisymm x) (hs : w.IsSol x) : w.res x ∈ w.Sol :=
  fun r hr => by rw [eval_congr (fun a b h => lay_res hx h) hr]; exact hs r hr

lemma exists_sol : ∃ y, y ∈ w.Sol := by
  obtain ⟨h, ⟨hinj, hsol⟩, -⟩ := exists_flat _ w rfl
  exact ⟨_, res_mem_Sol (antisymm_xOf hinj) hsol⟩

lemma zmod2_add_add (a b : ZMod 2) : a + (b + a) = b := by
  revert a b; decide

/-- The solutions form a coset of the kernel. -/
lemma Sol_eq {y₀ : w.Var → ZMod 2} (h₀ : y₀ ∈ w.Sol) :
    w.Sol = (fun z => y₀ + z) '' (LinearMap.ker w.rowMap : Set (w.Var → ZMod 2)) := by
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
  constructor
  · intro hy
    refine ⟨y + y₀, ?_, funext fun u => zmod2_add_add _ _⟩
    funext r
    rw [map_add, Pi.add_apply, (mem_Sol_iff y).1 hy r, (mem_Sol_iff y₀).1 h₀ r, Pi.zero_apply]
    exact zmod2_add_self _
  · rintro ⟨z, hz, rfl⟩
    rw [mem_Sol_iff]
    intro r
    rw [map_add, Pi.add_apply, hz, Pi.zero_apply, add_zero]
    exact (mem_Sol_iff y₀).1 h₀ r

/-- The adjacent variables, as a linear map to functions on the creases. -/
noncomputable def adjMap (w : Walk ι α) : (w.Var → ZMod 2) →ₗ[ZMod 2] (w.C → ZMod 2) where
  toFun y := fun k => hat y (w.adj k.1)
  map_add' y y' := by funext k; exact hat_add y y' _
  map_smul' c y := by funext k; exact hat_smul c y _

lemma asg_lay_add (y z : w.Var → ZMod 2) :
    w.asg (lay (y + z)) = w.asg (lay y) + w.adjMap z := by
  funext k
  simp only [asg, lay_apply, hat_add, Pi.add_apply, adjMap, LinearMap.coe_mk, AddHom.coe_mk, adj]
  ring

lemma asg_lay_res {x : ι → ι → ZMod 2} (hx : w.Antisymm x) : w.asg (lay (w.res x)) = w.asg x := by
  funext k
  simp only [asg]
  rw [lay_res hx (adj_mem_ovPairs k.2)]

/-- The adjacent variables on the kernel. -/
noncomputable def adjK (w : Walk ι α) : LinearMap.ker w.rowMap →ₗ[ZMod 2] (w.C → ZMod 2) :=
  w.adjMap.comp (LinearMap.ker w.rowMap).subtype

/-- `W_lin` is a translate of the image of the kernel. -/
lemma Wlin_eq {y₀ : w.Var → ZMod 2} (h₀ : y₀ ∈ w.Sol) :
    w.Wlin = (fun δ => w.asg (lay y₀) + δ) '' (LinearMap.range w.adjK : Set (w.C → ZMod 2)) := by
  ext σ
  simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx, hs, rfl⟩
    have hy := res_mem_Sol hx hs
    rw [Sol_eq h₀] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    refine ⟨_, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
    rw [← asg_lay_res hx, ← hyz, asg_lay_add]
    rfl
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    have hy : y₀ + z.1 ∈ w.Sol := by
      rw [Sol_eq h₀]; exact ⟨z.1, z.2, rfl⟩
    exact ⟨lay (y₀ + z.1), antisymm_lay _, hy, by rw [asg_lay_add]; rfl⟩

/-! ### Proposition 2 -/

/-- **Proposition 2 (rank at a generic vertex).**  At a vertex without taco–taco rows (in
particular at a generic vertex) of degree `2m`, with `N` overlapping pairs and `c` components of
`R_v` without adjacent pairs (its cycles): `m = γ`, the rows have rank `N - m - c`, they have
`2^(m + c)` solutions, and every flat-foldable assignment is induced by exactly `2^c` of them. -/
theorem prop1 (hn : w.NoTC) :
    2 * w.gamma = w.C.card ∧
    Module.finrank (ZMod 2) (LinearMap.range w.rowMap) = w.ovPairs.card - w.gamma - w.cyc ∧
    w.Sol.ncard = 2 ^ (w.gamma + w.cyc) ∧
    ∀ σ ∈ w.Wflat, {y | y ∈ w.Sol ∧ w.asg (lay y) = σ}.ncard = 2 ^ w.cyc := by
  obtain ⟨c⟩ := exists_chain _ w rfl
  obtain ⟨hcard, hgam, -⟩ := card_Wlin c
  have hE := E_generic c hn
  have h2 : 2 * w.gamma = w.C.card := by rw [hgam]; exact hE
  obtain ⟨y₀, h₀⟩ := exists_sol (w := w)
  have hk := finrank_ker hn
  rw [card_comps] at hk
  -- `W_lin` has `2^γ` elements, so the adjacent variables have rank `γ` on the kernel
  have hWl : w.Wlin.ncard = 2 ^ w.gamma := by rw [hcard, hgam]; congr 1; omega
  have hrg : Module.finrank (ZMod 2) (LinearMap.range w.adjK) = w.gamma := by
    rw [Wlin_eq h₀, Set.ncard_image_of_injective _ (add_right_injective _),
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, natCard_eq_two_pow] at hWl
    exact Nat.pow_right_injective le_rfl hWl
  have hk0 : Module.finrank (ZMod 2) (LinearMap.ker w.adjK) = w.cyc := by
    have := LinearMap.finrank_range_add_finrank_ker w.adjK
    rw [hrg, hk] at this
    omega
  refine ⟨h2, ?_, ?_, ?_⟩
  · have h := LinearMap.finrank_range_add_finrank_ker w.rowMap
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hk] at h
    omega
  · rw [Sol_eq h₀, Set.ncard_image_of_injective _ (add_right_injective _), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, natCard_eq_two_pow, hk]
  · intro σ hσ
    have hσl : σ ∈ w.Wlin := Wflat_subset_Wlin hσ
    rw [Wlin_eq h₀] at hσl
    obtain ⟨_, ⟨z₀, rfl⟩, rfl⟩ := hσl
    -- the fibre is a translate of the kernel of the adjacent variables
    have hfib : {y | y ∈ w.Sol ∧ w.asg (lay y) = w.asg (lay y₀) + w.adjK z₀} =
        (fun z : LinearMap.ker w.adjK => y₀ + z₀.1 + z.1.1) '' Set.univ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_univ, true_and]
      constructor
      · rintro ⟨hy, ha⟩
        rw [Sol_eq h₀] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        have hz' : z + z₀.1 ∈ LinearMap.ker w.rowMap := Submodule.add_mem _ hz z₀.2
        refine ⟨⟨⟨z + z₀.1, hz'⟩, ?_⟩, ?_⟩
        · rw [LinearMap.mem_ker]
          show w.adjMap (z + z₀.1) = 0
          rw [asg_lay_add] at ha
          rw [map_add]
          have : w.adjMap z = w.adjMap z₀.1 := add_left_cancel ha
          rw [this]; funext k; exact zmod2_add_self _
        · funext u
          simp only [Pi.add_apply]
          generalize y₀ u = a; generalize z u = b; generalize z₀.1 u = d
          revert a b d; decide
      · rintro ⟨z, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [Sol_eq h₀]
          exact ⟨z₀.1 + z.1.1, Submodule.add_mem _ z₀.2 z.1.2, (add_assoc _ _ _).symm⟩
        · rw [asg_lay_add, asg_lay_add]
          have : w.adjMap z.1.1 = 0 := LinearMap.mem_ker.1 z.2
          rw [this, add_zero]; rfl
    rw [hfib, Set.ncard_image_of_injective _ (fun a b h => Subtype.ext (Subtype.ext
      (add_left_cancel h))), Set.ncard_univ, natCard_eq_two_pow, hk0]

end Walk

end Origami
