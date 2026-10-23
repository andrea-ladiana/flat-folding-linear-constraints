import Origami.Theorem1
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Pi

/-!
# Corollary 4: the vertex rows add no information

A crease pattern is seen through its interior vertices: every vertex `v` has a closed walk
`w v`, and its sector `k` is the facet `f v k` of the pattern (distinct sectors at a vertex
are distinct facets).  The layer variables of the pattern are functions `X : F → F → 𝔽₂`,
antisymmetric on distinct facets; they may be parametrized in any way (`X : Y → …`, for
instance by one bit per pair of facets), and the rows of all the vertices become functions on
the parameters, affine over `𝔽₂`.

By Theorem 1, the vertex row of every vertex is, as a function of the parameters, the sum of
the rows at that vertex.  Hence adding the vertex rows changes neither the span of the rows
(so neither the rank of the augmented system) nor the set of solutions; and a parity
certificate of non-foldability (a combination of rows equal to the constant `1`) never needs
a vertex row.
-/

set_option linter.unusedSectionVars false

namespace Origami

variable {ι : Type*} [LinearOrder ι]
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- A crease pattern seen through its interior vertices: the walk of every vertex, and the
facet of every sector. -/
structure Pattern (V ι F α : Type*) [LinearOrder ι] [LinearOrder α] where
  /-- the walk of the vertex `v` -/
  w : V → Walk ι α
  /-- the facet of the sector `k` at the vertex `v` -/
  f : V → ι → F
  inj : ∀ v, Set.InjOn (f v) (w v).C

namespace Pattern

variable {V F : Type*} (P : Pattern V ι F α)

/-- Layer variables of the pattern: antisymmetric on distinct facets. -/
def Anti (X : F → F → ZMod 2) : Prop := ∀ a b, a ≠ b → X b a = X a b + 1

/-- The layer variables at the vertex `v`. -/
def loc (X : F → F → ZMod 2) (v : V) : ι → ι → ZMod 2 := fun i j => X (P.f v i) (P.f v j)

lemma antisymm_loc {X : F → F → ZMod 2} (hX : Anti X) (v : V) : (P.w v).Antisymm (P.loc X v) :=
  fun _ hi _ hj hij => hX _ _ (fun e => hij (P.inj v hi hj e))

variable {Y : Type*}

/-- The rows of the pattern (a vertex and a row at it), as functions of the parameters. -/
def rowFun (X : Y → F → F → ZMod 2) (p : Σ v, (P.w v).rows) : Y → ZMod 2 :=
  fun y => p.2.1.eval (P.loc (X y) p.1)

/-- The vertex row of `v`, `∑_k x_{k,k+1} + 1`, as a function of the parameters. -/
def vertexFun (X : Y → F → F → ZMod 2) (v : V) : Y → ZMod 2 :=
  fun y => ∑ k ∈ (P.w v).C, P.loc (X y) v k (nxt (P.w v).C k) + 1

/-- Theorem 1 in the pattern: every vertex row is the sum of the rows at its vertex. -/
theorem vertexFun_eq_sum {X : Y → F → F → ZMod 2} (hX : ∀ y, Anti (X y)) (v : V) :
    P.vertexFun X v = ∑ r : (P.w v).rows, P.rowFun X ⟨v, r⟩ := by
  funext y
  simp only [vertexFun, rowFun, Finset.sum_apply]
  rw [← Walk.sum_rows_eq_vertex_row (P.antisymm_loc (hX y) v)]
  exact (Finset.sum_coe_sort _ _).symm

/-- **Corollary 4 (no new information in the vertex rows).**  Adding the vertex rows of all the
interior vertices to the rows of a pattern changes neither their span (hence the rank of the
system) nor its set of solutions, and a parity certificate (a combination of rows equal to the
constant `1`) exists with the vertex rows iff it exists without them. -/
theorem corollary4 {X : Y → F → F → ZMod 2} (hX : ∀ y, Anti (X y)) :
    Submodule.span (ZMod 2) (Set.range (P.rowFun X) ∪ Set.range (P.vertexFun X)) =
      Submodule.span (ZMod 2) (Set.range (P.rowFun X)) ∧
    {y | ∀ p, P.rowFun X p y = 0} =
      {y | (∀ p, P.rowFun X p y = 0) ∧ ∀ v, P.vertexFun X v y = 0} ∧
    ((fun _ => 1) ∈ Submodule.span (ZMod 2) (Set.range (P.rowFun X) ∪ Set.range (P.vertexFun X))
      ↔ (fun _ => 1) ∈ Submodule.span (ZMod 2) (Set.range (P.rowFun X))) := by
  have hspan : Submodule.span (ZMod 2) (Set.range (P.rowFun X) ∪ Set.range (P.vertexFun X)) =
      Submodule.span (ZMod 2) (Set.range (P.rowFun X)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro φ (⟨p, rfl⟩ | ⟨v, rfl⟩)
      · exact Submodule.subset_span ⟨p, rfl⟩
      · rw [P.vertexFun_eq_sum hX v]
        exact Submodule.sum_mem _ fun r _ => Submodule.subset_span ⟨⟨v, r⟩, rfl⟩
    · exact Submodule.span_mono Set.subset_union_left
  refine ⟨hspan, ?_, by rw [hspan]⟩
  ext y
  simp only [Set.mem_setOf_eq]
  refine ⟨fun h => ⟨h, fun v => ?_⟩, fun h => h.1⟩
  rw [P.vertexFun_eq_sum hX v, Finset.sum_apply]
  exact Finset.sum_eq_zero fun r _ => h ⟨v, r⟩

end Pattern

end Origami
