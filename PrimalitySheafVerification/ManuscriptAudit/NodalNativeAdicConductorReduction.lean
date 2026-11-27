import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeConductorNaturality
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleHausdorffDirectImage

/-! The actual native adic conductor class has as each finite
reduction the conductor class with the actual reduced coefficient. -/

namespace ManuscriptAudit.NodalNativeAdicConductorReduction

open AlgebraicGeometry CategoryTheory Opposite
open NodalProjectiveClosure (projectiveNode)
open NodalNativeConductorHOne (boundary boundary_injective boundary_surjective)
open NodalNativeConductorNaturality (boundary_natural)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleContinuousCoefficientNaturality (map)
open ProetaleResidueSheaves (residueReduction residueTransition)
open EtaleProetaleHausdorffDirectImage (DiscreteGroup discreteEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev X := projectiveNode K
private abbrev D := DiscreteGroup ℤ_[ℓ]
private abbrev lift := sheafCompose (Scheme.ProEt.topology (X K)) AddCommGrpCat.uliftFunctor.{1}

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

abbrev reduction (n : ℕ) := (lift K).map (residueReduction (X K) ℓ n)
abbrev transition (n : ℕ) := (lift K).map (residueTransition (X K) ℓ n)

/-- The actual finite label maps into the corresponding native finite-residue H¹. -/
abbrev finiteLabel (n : ℕ) :
    ZMod (ℓ ^ n) →+ Sheaf.H (finiteCoefficient (X K) ℓ n) 1 :=
  boundary K h2 (ZMod (ℓ ^ n))

private abbrev fromDiscrete := (discreteEquiv ℤ_[ℓ]).toAddMonoidHom

private abbrev discretely (n : ℕ) : D ℓ →+ ZMod (ℓ ^ n) :=
  (PadicInt.toZModPow n).toAddMonoidHom.comp (fromDiscrete ℓ)

private abbrev toAdic :=
  map (fromDiscrete ℓ) continuous_of_discreteTopology (X K)

/-- Actual native integral conductor class, via the continuous arrow
from its discrete coefficient copy to the adic coefficient sheaf. -/
def integralBoundary : ℤ_[ℓ] →+ (X K).EllAdicCohomology ℓ 1 :=
  (Sheaf.H.map (toAdic K ℓ) 1).comp
    ((boundary K h2 (D ℓ)).comp (discreteEquiv ℤ_[ℓ]).symm.toAddMonoidHom)

private theorem toAdic_reduction (n : ℕ) :
    toAdic K ℓ ≫ reduction K ℓ n =
      map (discretely ℓ n) continuous_of_discreteTopology (X K) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

theorem integralBoundary_reduction (n : ℕ) (a : ℤ_[ℓ]) :
    Sheaf.H.map (reduction K ℓ n) 1 (integralBoundary K h2 ℓ a) =
      finiteLabel K h2 ℓ n (PadicInt.toZModPow n a) := by
  let c : D ℓ := (discreteEquiv ℤ_[ℓ]).symm a
  let z := boundary K h2 (D ℓ) c
  change Sheaf.H.map (reduction K ℓ n) 1 (Sheaf.H.map (toAdic K ℓ) 1 z) = _
  calc
    _ = Sheaf.H.map (toAdic K ℓ ≫ reduction K ℓ n) 1 z :=
      (Sheaf.H.map_comp_apply (toAdic K ℓ) (reduction K ℓ n) z).symm
    _ = Sheaf.H.map (map (discretely ℓ n) continuous_of_discreteTopology (X K)) 1 z :=
      congrArg (fun f : ProetaleContinuousDirectImageMaps.functions (D ℓ) (X K) ⟶
        finiteCoefficient (X K) ℓ n ↦ Sheaf.H.map f 1 z) (toAdic_reduction K ℓ n)
    _ = finiteLabel K h2 ℓ n (discretely ℓ n c) :=
      boundary_natural K h2 (discretely ℓ n) continuous_of_discreteTopology c
    _ = _ := by
      change finiteLabel K h2 ℓ n (PadicInt.toZModPow n
        ((discreteEquiv ℤ_[ℓ]) ((discreteEquiv ℤ_[ℓ]).symm a))) = _
      rw [AddEquiv.apply_symm_apply]

theorem finiteLabel_transition (n : ℕ) (a : ZMod (ℓ ^ (n + 1))) :
    Sheaf.H.map (transition K ℓ n) 1 (finiteLabel K h2 ℓ (n + 1) a) =
      finiteLabel K h2 ℓ n (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a) :=
  boundary_natural K h2 (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom
    continuous_of_discreteTopology a

end
end ManuscriptAudit.NodalNativeAdicConductorReduction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeAdicConductorReduction.integralBoundary_reduction,
      ``ManuscriptAudit.NodalNativeAdicConductorReduction.finiteLabel_transition] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
