import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeConductorHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousCoefficientNaturality

/-! The actual conductor boundary is natural in the discrete coefficient
group, so its finite identifications preserve native reduction maps. -/

namespace ManuscriptAudit.NodalNativeConductorNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizationMap)
open NodalSmoothRationalBoundary (projectiveOrigin)
open NodalProetaleConductorBinary (plus minus plus_over minus_over)
open NodalProetaleConductorSequence (sequence_shortExact)
open NodalProetaleConductorHZero (originHZeroEquiv)
open NodalNativeConductorHOne (boundary)
open ProetaleContinuousCoefficientNaturality (map mapOver sequenceMap HZeroEquiv_mapOver)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
  [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
variable (f : M →+ N) (hf : Continuous f)

theorem originHZero_natural (x : Sheaf.H
    (ProetaleContinuousDirectImageMaps.functionsOver M (projectiveOrigin K)) 0) :
    originHZeroEquiv K N (Sheaf.H.map (mapOver f hf (projectiveOrigin K)) 0 x) =
      f (originHZeroEquiv K M x) :=
  HZeroEquiv_mapOver f hf (projectiveOrigin K) x (IsLocalRing.closedPoint K)

/-- Natural connecting map for the actual proper conductor short exact sequence. -/
theorem boundary_natural (m : M) :
    Sheaf.H.map (map f hf (projectiveNode K)) 1 (boundary K h2 M m) =
      boundary K h2 N (f m) := by
  let φ := sequenceMap f hf (normalizationMap K) (projectiveOrigin K)
    (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2)
  let h₁ := sequence_shortExact K h2 M
  let h₂ := sequence_shortExact K h2 N
  let x := (originHZeroEquiv K M).symm m
  have hx : Sheaf.H.map φ.τ₃ 0 x = (originHZeroEquiv K N).symm (f m) := by
    apply (originHZeroEquiv K N).injective
    rw [AddEquiv.apply_symm_apply]
    change originHZeroEquiv K N (Sheaf.H.map (mapOver f hf (projectiveOrigin K)) 0 x) = f m
    rw [originHZero_natural, x, AddEquiv.apply_symm_apply]
  change (x.comp h₁.extClass (show 0 + 1 = 1 by rfl)).comp (Ext.mk₀ φ.τ₁) (add_zero 1) =
    ((originHZeroEquiv K N).symm (f m)).comp h₂.extClass (show 0 + 1 = 1 by rfl)
  rw [← hx, Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ]

end
end ManuscriptAudit.NodalNativeConductorNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeConductorNaturality.originHZero_natural,
      ``ManuscriptAudit.NodalNativeConductorNaturality.boundary_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
