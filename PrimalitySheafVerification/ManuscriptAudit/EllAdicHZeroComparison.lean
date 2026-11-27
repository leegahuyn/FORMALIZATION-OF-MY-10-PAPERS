import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricBoundary

/-! Degree zero of Mathlib's actual pro-étale ℓ-adic coefficient sheaf. -/

namespace ManuscriptAudit.EllAdicHZeroComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IntegralNodalGeometricFiber (geometricFiber closureField)
open IntegralNodalGeometricBoundary (origin geometric_preconnected)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Actual pro-étale ℓ-adic H⁰ is the additive group of continuous p-adic-valued functions. -/
def continuousEquiv : X.EllAdicCohomology ℓ 0 ≃+ C(X, ℤ_[ℓ]) := by
  let T := Scheme.ProEt.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  let F := (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)
  let e : F.obj.obj (op T) ≃+ C(X, ℤ_[ℓ]) := AddEquiv.ulift
  exact (Sheaf.H.equiv₀ F hT).trans e

/-- On a nonempty preconnected scheme the actual pro-étale ℓ-adic H⁰ is the coefficient group. -/
def connectedEquiv [PreconnectedSpace X] (x : X) : X.EllAdicCohomology ℓ 0 ≃+ ℤ_[ℓ] := by
  let e : C(X, ℤ_[ℓ]) ≃+ ℤ_[ℓ] :=
    { toFun := fun f ↦ f x
      invFun := ContinuousMap.const X
      left_inv := fun f ↦ by
        apply ContinuousMap.ext
        intro y
        exact TotallyDisconnectedSpace.eq_of_continuous f f.continuous x y
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  exact (continuousEquiv X ℓ).trans e

/-- The literal proper nodal geometric fibre has the actual pro-étale ℓ-adic H⁰ equal to ℤℓ. -/
def properFiberEquiv (p : ℕ) [Fact p.Prime] :
    (geometricFiber p).EllAdicCohomology ℓ 0 ≃+ ℤ_[ℓ] := by
  letI := geometric_preconnected p
  let T := Spec (CommRingCat.of (closureField p))
  let x : T := Classical.choice (inferInstance : Nonempty T)
  exact connectedEquiv (geometricFiber p) ℓ (origin p x)

end
end ManuscriptAudit.EllAdicHZeroComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EllAdicHZeroComparison.continuousEquiv,
      ``ManuscriptAudit.EllAdicHZeroComparison.connectedEquiv,
      ``ManuscriptAudit.EllAdicHZeroComparison.properFiberEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
