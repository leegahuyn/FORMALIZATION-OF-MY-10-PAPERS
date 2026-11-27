import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCyclicInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricInverseLimit

/-! Additive inverse limits along the actual coefficient reductions in characteristic two. -/

namespace ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit

open AlgebraicGeometry CategoryTheory
open IntegralNodalCharacteristicTwoGeometry (coefficientField)
open IntegralNodalGeometricFiber (geometricFiber)
open IntegralNodalGeometricBoundary (geometricSmoothOpen)
open IntegralNodalGeometricPrimePower (affineCompactifyingOpen properHc affineHc smoothHc)
open IntegralNodalCharacteristicTwoCohomology (properPrimePowerEquiv affinePrimePowerEquiv
  smoothPrimePowerEquiv)
open IntegralNodalGeometricInverseLimit (properLimit affineLimit smoothLimit)
open OpenEtaleCoefficientReduction (reductionH reductionH_surjective)
open OpenEtaleCyclicInverseLimit (padicEquiv)

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

private abbrev jProper := 𝟙 (geometricFiber 2)
private abbrev jAffine := affineCompactifyingOpen 2
private abbrev jSmooth := (geometricSmoothOpen 2).ι

private theorem trivial_of_equiv {B : Type} [AddCommGroup B] (e : B ≃+ ZMod 1) :
    Subsingleton B :=
  ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

private theorem prime_cast_ne_zero (hℓ₂ : ℓ ≠ 2) : (ℓ : coefficientField) ≠ 0 :=
  IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂

/-- The actual coefficient reductions are surjective in proper degrees zero and two. -/
theorem proper_reduction_onto (hℓ₂ : ℓ ≠ 2) (r n : ℕ) (hn : n = 0 ∨ n = 2) :
    Function.Surjective (reductionH jProper (ℓ ^ r) ℓ n) := by
  letI : NeZero (ℓ : coefficientField) := ⟨prime_cast_ne_zero ℓ hℓ₂⟩
  rcases hn with rfl | rfl
  · have h : Subsingleton (properHc 2 ℓ 1) :=
      trivial_of_equiv (IntegralNodalCharacteristicTwoCohomology.properEquiv ℓ 1)
    exact reductionH_surjective jProper (ℓ ^ r) ℓ 0 h
  · have h : Subsingleton (properHc 2 ℓ 3) :=
      trivial_of_equiv (IntegralNodalCharacteristicTwoCohomology.properEquiv ℓ 3)
    exact reductionH_surjective jProper (ℓ ^ r) ℓ 2 h

/-- The actual coefficient reductions are surjective in compact degree two of the affine chart. -/
theorem affine_reduction_onto (hℓ₂ : ℓ ≠ 2) (r : ℕ) :
    Function.Surjective (reductionH jAffine (ℓ ^ r) ℓ 2) := by
  letI : NeZero (ℓ : coefficientField) := ⟨prime_cast_ne_zero ℓ hℓ₂⟩
  have h : Subsingleton (affineHc 2 ℓ 3) :=
    trivial_of_equiv (IntegralNodalCharacteristicTwoCohomology.affineEquiv ℓ 3)
  exact reductionH_surjective jAffine (ℓ ^ r) ℓ 2 h

/-- The actual coefficient reductions are surjective in compact degree two of the relative smooth open. -/
theorem smooth_reduction_onto (hℓ₂ : ℓ ≠ 2) (r : ℕ) :
    Function.Surjective (reductionH jSmooth (ℓ ^ r) ℓ 2) := by
  letI : NeZero (ℓ : coefficientField) := ⟨prime_cast_ne_zero ℓ hℓ₂⟩
  have h : Subsingleton (smoothHc 2 ℓ 3) :=
    trivial_of_equiv (IntegralNodalCharacteristicTwoCohomology.smoothEquiv ℓ 3)
  exact reductionH_surjective jSmooth (ℓ ^ r) ℓ 2 h

/-- Ordinary additive inverse limits of the proper geometric fibre in degrees zero and two. -/
def properEquiv (hℓ₂ : ℓ ≠ 2) (n : ℕ) (hn : n = 0 ∨ n = 2) :
    properLimit 2 ℓ n ≃+ ℤ_[ℓ] :=
  padicEquiv jProper ℓ n (fun r ↦ proper_reduction_onto ℓ hℓ₂ r n hn)
    (fun r ↦ (properPrimePowerEquiv ℓ hℓ₂ r n).trans (ZMod.ringEquivCongr (if_pos hn)).toAddEquiv)

/-- Ordinary additive inverse limit of the actual affine geometric chart in degree two. -/
def affineEquiv (hℓ₂ : ℓ ≠ 2) :
    affineLimit 2 ℓ 2 ≃+ ℤ_[ℓ] :=
  padicEquiv jAffine ℓ 2 (affine_reduction_onto ℓ hℓ₂)
    (fun r ↦ affinePrimePowerEquiv ℓ hℓ₂ r 2)

/-- Ordinary additive inverse limit of the actual relative smooth open in degree two. -/
def smoothEquiv (hℓ₂ : ℓ ≠ 2) :
    smoothLimit 2 ℓ 2 ≃+ ℤ_[ℓ] :=
  padicEquiv jSmooth ℓ 2 (smooth_reduction_onto ℓ hℓ₂)
    (fun r ↦ smoothPrimePowerEquiv ℓ hℓ₂ r 2)

end
end ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit.proper_reduction_onto,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit.affine_reduction_onto,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit.smooth_reduction_onto,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit.properEquiv,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit.affineEquiv,
      ``ManuscriptAudit.IntegralNodalCharacteristicTwoInverseLimit.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
