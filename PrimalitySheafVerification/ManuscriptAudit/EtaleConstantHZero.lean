import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.CuspProperBoundary
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero

/-!
# Constant étale sections on a preconnected scheme and on the proper cusp

The verified continuous-map presentation of the constant sheaf gives
the actual small étale H⁰ at any chosen point on a preconnected scheme.
The proper cusp is nonempty and preconnected, so its constant H⁰ is
its coefficient group.
-/

namespace ManuscriptAudit.EtaleConstantHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleContinuousMapSheaf CuspProperCompactification

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private def continuousMapEvalEquiv (X : Scheme.{u}) [PreconnectedSpace X]
    (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M]
    [IsTopologicalAddGroup M] (x : X) : C(X, M) ≃+ M where
  toFun f := f x
  invFun := ContinuousMap.const X
  left_inv f := by
    apply ContinuousMap.ext
    intro y
    exact TotallyDisconnectedSpace.eq_of_continuous f f.continuous x y
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Actual constant étale H⁰ of a preconnected scheme, evaluated at a point. -/
def constantHZeroEquiv (X : Scheme.{u}) [PreconnectedSpace X]
    (M : AddCommGrpCat.{u}) (x : X) :
    Sheaf.H ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M) 0 ≃+ M := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  let W := Scheme.Etale.mk (𝟙 X)
  let hW : IsTerminal W := MorphismProperty.Over.mkIdTerminal @Etale X
  let F := continuousMapSheaf X M
  let e := ((Sheaf.functorH X.smallEtaleTopology 0).mapIso
    (constantSheafContinuousMapIso X M)).addCommGroupIsoToAddEquiv
  let e₀ : Sheaf.H F 0 ≃+ C(X, M) := Sheaf.H.equiv₀ F hW
  exact e.trans (e₀.trans (continuousMapEvalEquiv X M x))

/-- Actual constant étale H⁰ of the proper closure is the coefficient group. -/
def cuspConstantHZeroEquiv (K : Type u) [Field K] (M : AddCommGrpCat.{u}) :
    Sheaf.H ((constantSheaf (projectiveCusp K).smallEtaleTopology AddCommGrpCat.{u}).obj M) 0 ≃+ M := by
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  have h : Nonempty (projectiveCusp K) := by
    obtain ⟨x, _⟩ := CuspProperBoundary.boundary_nonempty K
    exact ⟨x⟩
  exact constantHZeroEquiv (projectiveCusp K) M (Classical.choice h)

end

end ManuscriptAudit.EtaleConstantHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.EtaleConstantHZero.constantHZeroEquiv,
      ``ManuscriptAudit.EtaleConstantHZero.cuspConstantHZeroEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
