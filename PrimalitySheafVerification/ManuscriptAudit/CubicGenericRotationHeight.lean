import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalShiftedRotation
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericSecantHeight
import PrimalitySheafVerification.ManuscriptAudit.RotationHeightArithmetic
import PrimalitySheafVerification.ManuscriptAudit.CubicRationalPointHeight

/-! The exact generic Kummer height of the actual integral shift [c]−ρ is c²+c+1. -/

namespace ManuscriptAudit.CubicGenericRotationHeight

open Polynomial WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace
open CubicGenericFunctionField CubicGenericAntiInvariant CubicGenericPointHeight
open CubicGenericFrobeniusHeight CubicGenericSecantHeight RationalSubstitutionDegree
open CubicNaturalPointEnd CubicNaturalCMOperations CubicNaturalShiftedRotation

noncomputable section
open scoped Classical

universe u

variable {K : Type u} [Field K] {A z : K}

private theorem height_of_scaled_x (P : antiInvariant A) {d : K} (hd : d ≠ 0)
    (hP : P.val.xRep = ![algebraMap K (Model A) d * genericX A, 1]) :
    height A P = 1 := by
  let r := algebraMap K[X] (RatFunc K) (C d * X)
  have hR : algebraMap (RatFunc K) (Model A) r =
      algebraMap K (Model A) d * genericX A := by
    simp only [r, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X, genericX]
    rfl
  have hRep : P.val.xRep = ![algebraMap (RatFunc K) (Model A) r, 1] := by rw [hR, hP]
  rw [CubicRationalPointHeight.height_eq_of_xRep A P r hRep]
  change max r.num.natDegree r.denom.natDegree = 1
  rw [show r = algebraMap K[X] (RatFunc K) (C d * X) from rfl,
    RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_C_mul hd, natDegree_X,
    natDegree_one, max_zero_right]

/-- The generic point, its actual rotation, and their sum have height one. -/
theorem generic_rotation_heights
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) :
    let Q := genericAntiPoint A h₂ h₃ hA
    let R := antiInvariantApply (rotation h₂ h₃ hA hz) Q
    height A Q = 1 ∧ height A R = 1 ∧ height A (Q + R) = 1 := by
  let M := Model A
  let Q := genericAntiPoint A h₂ h₃ hA
  let r := rotation h₂ h₃ hA hz
  let R := antiInvariantApply r Q
  let S := antiInvariantApply r R
  have hZ : z ≠ 0 := by
    intro h
    simpa [h] using hz
  obtain ⟨hQ, eQ⟩ : ∃ h, Q.val = .some (genericX A) (genericY A) h := ⟨_, rfl⟩
  obtain ⟨hR, eR⟩ := rotation_some h₂ h₃ hA hz hQ
  have hR' : R.val = .some (algebraMap K M z * genericX A) (genericY A) hR := by
    change r.atField M Q.val = _
    rw [eQ, eR]
  have hHR : height A R = 1 := height_of_scaled_x R hZ (by rw [hR'] <;> rfl)
  obtain ⟨hS, eS⟩ := rotation_some h₂ h₃ hA hz hR
  have hS' : S.val =
      .some (algebraMap K M z * (algebraMap K M z * genericX A)) (genericY A) hS := by
    change r.atField M R.val = _
    rw [hR', eS]
  have hHS : height A S = 1 := height_of_scaled_x S (pow_ne_zero 2 hZ) (by
    rw [hS']
    change ![algebraMap K M z * (algebraMap K M z * genericX A), 1] =
      ![algebraMap K M (z ^ 2) * genericX A, 1]
    rw [map_pow, pow_two, mul_assoc])
  have hQRS : Q + R = -S := by
    apply Subtype.ext
    have h := congrArg (fun f : AddMonoid.End (GeometricPoints K M A) => f Q.val)
      (rotation_quadratic h₂ h₃ hA hz M hz₁)
    change S.val + R.val + Q.val = 0 at h
    change Q.val + R.val = -S.val
    calc
      _ = (S.val + R.val + Q.val) - S.val := by abel
      _ = _ := by rw [h, zero_sub]
  have hNeg := (quadraticHeight A h₂ h₃ hA).map_neg S
  change (height A (-S) : ℤ) = (height A S : ℤ) at hNeg
  have hNeg' : height A (-S) = height A S := by exact_mod_cast hNeg
  exact ⟨CubicRationalPointHeight.generic_point_height A h₂ h₃ hA, hHR, by rw [hQRS, hNeg', hHS]⟩

/-- The actual operator [c]−ρ has the expected exact integral degree at the generic point. -/
theorem shifted_height (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (c : ℤ) :
    (height A (antiInvariantApply (shifted h₂ h₃ hA hz c) (genericAntiPoint A h₂ h₃ hA)) :
      ℤ) = c ^ 2 + c + 1 := by
  let Q := genericAntiPoint A h₂ h₃ hA
  let R := antiInvariantApply (rotation h₂ h₃ hA hz) Q
  let D := quadraticHeight A h₂ h₃ hA
  obtain ⟨hQ₀, hR₀, hS₀⟩ := generic_rotation_heights h₂ h₃ hA hz hz₁
  have hQ : D Q = 1 := by
    change (height A Q : ℤ) = 1
    exact_mod_cast hQ₀
  have hR : D R = 1 := by
    change (height A R : ℤ) = 1
    exact_mod_cast hR₀
  have hS : D (Q + R) = 1 := by
    change (height A (Q + R) : ℤ) = 1
    exact_mod_cast hS₀
  have he : antiInvariantApply (shifted h₂ h₃ hA hz c) Q = c • Q - R := Subtype.ext rfl
  change D (antiInvariantApply (shifted h₂ h₃ hA hz c) Q) = _
  rw [he]
  exact RotationHeightArithmetic.integer_shift_height D Q R hQ hR hS c

end

end ManuscriptAudit.CubicGenericRotationHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericRotationHeight.generic_rotation_heights,
      ``ManuscriptAudit.CubicGenericRotationHeight.shifted_height] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
