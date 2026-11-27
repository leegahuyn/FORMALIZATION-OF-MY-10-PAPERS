import Lean.Util.CollectAxioms
import Mathlib.Topology.KrullDimension

/-! A point's coheight is unchanged in an open neighborhood. Thus the
Krull dimension of a sober space is bounded by a common bound for
the members of any open cover. -/

namespace ManuscriptAudit.TopologicalKrullDimensionOpenCover

open TopologicalSpace TopologicalSpace.IrreducibleCloseds Topology Order

attribute [local instance] specializationOrder

/-- In a quasisober (T_0) space the Krull dimension is the supremum
of the coheights of its points in the specialization order. -/
theorem eq_iSup_point_coheight (X : Type*) [TopologicalSpace X] [QuasiSober X] [T0Space X] :
    topologicalKrullDim X = ⨆ x : X, (Order.coheight x : WithBot ℕ∞) := by
  unfold topologicalKrullDim
  rw [Order.krullDim_eq_iSup_coheight]
  let e := irreducibleSetEquivPoints (α := X)
  apply le_antisymm
  · refine iSup_le fun Z => ?_
    have h : Order.coheight (e Z) = Order.coheight Z := Order.coheight_orderIso e Z
    rw [← h]
    exact le_iSup (fun x : X => (Order.coheight x : WithBot ℕ∞)) (e Z)
  · refine iSup_le fun x => ?_
    have h : Order.coheight (e.symm x) = Order.coheight x :=
      Order.coheight_orderIso e.symm x
    rw [← h]
    exact le_iSup (fun Z : IrreducibleCloseds X => (Order.coheight Z : WithBot ℕ∞)) (e.symm x)

/-- A common dimension bound on an open cover is a dimension bound on
the ambient quasisober space. The cover is specified by its open embeddings. -/
theorem le_of_open_cover {X ι : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {U : ι → Type*} [∀ i, TopologicalSpace (U i)] [∀ i, QuasiSober (U i)]
    [∀ i, T0Space (U i)] (f : ∀ i, U i → X) (hOpen : ∀ i, IsOpenEmbedding (f i))
    (hCover : ∀ x : X, ∃ i, ∃ y : U i, f i y = x)
    (n : WithBot ℕ∞) (hBound : ∀ i, topologicalKrullDim (U i) ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [eq_iSup_point_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨i, y, rfl⟩ := hCover x
  rw [Topology.IsOpenEmbedding.coheight_eq (f i) (hOpen i)]
  have h := hBound i
  rw [eq_iSup_point_coheight] at h
  exact (le_iSup (fun z : U i => (Order.coheight z : WithBot ℕ∞)) y).trans h

end ManuscriptAudit.TopologicalKrullDimensionOpenCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.TopologicalKrullDimensionOpenCover.eq_iSup_point_coheight,
      ``ManuscriptAudit.TopologicalKrullDimensionOpenCover.le_of_open_cover] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
