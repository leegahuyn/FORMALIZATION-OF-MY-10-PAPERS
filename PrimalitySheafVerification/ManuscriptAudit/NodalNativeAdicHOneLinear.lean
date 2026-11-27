import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicScalarAction

/-! The native degree-one conductor identifies the split proper node's
actual cohomology line with the p-adic integers as a module. -/

namespace ManuscriptAudit.NodalNativeAdicHOneLinear

open AlgebraicGeometry CategoryTheory Opposite
open NodalProjectiveClosure (projectiveNode)
open NodalNativeAdicConductorReduction (integralBoundary)
open NodalNativeConductorHOne (boundary)
open NodalNativeConductorNaturality (boundary_natural)
open ProetaleContinuousCoefficientNaturality (map)
open NativeAdicScalarAction (adicModule multiply scalarMap)
open EtaleProetaleHausdorffDirectImage (DiscreteGroup discreteEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev X := projectiveNode K
private abbrev D := DiscreteGroup ℤ_[ℓ]
private abbrev d := discreteEquiv ℤ_[ℓ]
private abbrev toAdic := map (d ℓ).toAddMonoidHom continuous_of_discreteTopology (X K)

local instance : Module ℤ_[ℓ] ((X K).EllAdicCohomology ℓ 1) := adicModule (X K) ℓ 1

private abbrev discreteScalar (r : ℤ_[ℓ]) : D ℓ →+ D ℓ :=
  (d ℓ).symm.toAddMonoidHom.comp ((multiply ℓ r).comp (d ℓ).toAddMonoidHom)

private theorem scalar_square (r : ℤ_[ℓ]) :
    toAdic K ℓ ≫ scalarMap (X K) ℓ r =
      map (discreteScalar ℓ r) continuous_of_discreteTopology (X K) ≫ toAdic K ℓ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  let v : C(U.unop.left, D ℓ) := s.down
  change r * d ℓ (v x) = d ℓ ((d ℓ).symm (r * d ℓ (v x)))
  exact ((d ℓ).apply_symm_apply _).symm

/-- The actual native integral conductor boundary is ℓ-adically linear. -/
theorem boundary_smul (r a : ℤ_[ℓ]) :
    integralBoundary K h2 ℓ (r • a) = r • integralBoundary K h2 ℓ a := by
  let c : D ℓ := (d ℓ).symm a
  let z := boundary K h2 (D ℓ) c
  let rD := map (discreteScalar ℓ r) continuous_of_discreteTopology (X K)
  change Sheaf.H.map (toAdic K ℓ) 1 (boundary K h2 (D ℓ) ((d ℓ).symm (r * a))) =
    Sheaf.H.map (scalarMap (X K) ℓ r) 1 (Sheaf.H.map (toAdic K ℓ) 1 z)
  symm
  calc
    _ = Sheaf.H.map (toAdic K ℓ ≫ scalarMap (X K) ℓ r) 1 z :=
      (Sheaf.H.map_comp_apply (toAdic K ℓ) (scalarMap (X K) ℓ r) z).symm
    _ = Sheaf.H.map (rD ≫ toAdic K ℓ) 1 z :=
      congrArg (fun f : ProetaleContinuousDirectImageMaps.functions (D ℓ) (X K) ⟶
        ProetaleContinuousDirectImageMaps.functions ℤ_[ℓ] (X K) ↦ Sheaf.H.map f 1 z)
        (scalar_square K ℓ r)
    _ = Sheaf.H.map (toAdic K ℓ) 1 (Sheaf.H.map rD 1 z) :=
      Sheaf.H.map_comp_apply rD (toAdic K ℓ) z
    _ = Sheaf.H.map (toAdic K ℓ) 1 (boundary K h2 (D ℓ) (discreteScalar ℓ r c)) :=
      congrArg (fun v ↦ Sheaf.H.map (toAdic K ℓ) 1 v)
        (boundary_natural K h2 (discreteScalar ℓ r) continuous_of_discreteTopology c)
    _ = _ := by
      change Sheaf.H.map (toAdic K ℓ) 1 (boundary K h2 (D ℓ)
        ((d ℓ).symm (r * d ℓ ((d ℓ).symm a)))) = _
      rw [AddEquiv.apply_symm_apply]

variable [IsAlgClosed K] [NeZero (ℓ : K)]

/-- The actual native degree-one cohomology is a free module of rank one,
with the linear equivalence given by the conductor class. -/
def adicHOneLinearEquiv : ℤ_[ℓ] ≃ₗ[ℤ_[ℓ]] ((X K).EllAdicCohomology ℓ 1) where
  toAddEquiv := (NodalNativeAdicHOne.adicHOneEquiv K h2 ℓ).symm
  map_smul' := boundary_smul K h2 ℓ

end
end ManuscriptAudit.NodalNativeAdicHOneLinear

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeAdicHOneLinear.boundary_smul,
      ``ManuscriptAudit.NodalNativeAdicHOneLinear.adicHOneLinearEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
