import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPhaseCocycle
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCriticalOddVanishing
import PrimalitySheafVerification.ManuscriptAudit.Paper8CrossCuspScalingWidths
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaTranslation
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelZeroMode

/-! Actual Floquet phases of the odd eta automorphy at infinity and the level-four zero cusp. -/

namespace ManuscriptAudit.Paper8OddCuspFloquetPhase

open UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8EtaHalfWeightPhase Paper8EtaPhaseCocycle
open Paper8EtaCriticalOddVanishing Paper8OddCrossCuspRows Paper8EtaCuspWidths
open Paper8CrossCuspScalingWidths Paper8ActualEtaTranslation
open scoped MatrixGroups

noncomputable section

theorem negativePhase_T_pow (m : ℤ) (z : ℍ) :
    negativePhase (ModularGroup.T ^ m) z =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / 24) := by
  have hZ : ((ModularGroup.T ^ m • z : ℍ) : ℂ) = (z : ℂ) + (m : ℂ) := by
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hD : denominator (ModularGroup.T ^ m) z = 1 := by
    simp [denominator, ModularGroup.coe_T_zpow]
  simp only [negativePhase, positivePhase, hZ, hD, norm_one, Real.sqrt_one, Complex.ofReal_one,
    mul_one, div_one, eta_add_integer, mul_div_cancel_right₀ _ (ModularForm.eta_ne_zero z.im_pos)]

private theorem negativePhase_ne_zero (g : SL(2, ℤ)) (z : ℍ) : negativePhase g z ≠ 0 := by
  intro h
  have hN := negativePhase_norm g z
  rw [h, norm_zero] at hN
  exact zero_ne_one hN

def cuspOddProfile (F : ℂ → ℂ) (g : SL(2, ℤ)) (z : ℍ) : ℂ :=
  F (g • z : ℍ) / negativePhase g z

theorem cuspOddProfile_shift {F : ℂ → ℂ} (hF : OddMaassLaw F)
    (g : SL(2, ℤ)) (m : ℤ)
    (hm : g * ModularGroup.T ^ m * g⁻¹ ∈ CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    cuspOddProfile F g (ModularGroup.T ^ m • z) =
      (levelCharacter ⟨g * ModularGroup.T ^ m * g⁻¹, hm⟩ : ℂ) *
        negativePhase (ModularGroup.T ^ m) z * cuspOddProfile F g z := by
  let t : SL(2, ℤ) := ModularGroup.T ^ m
  let h : CongruenceSubgroup.Gamma0 4 := ⟨g * t * g⁻¹, hm⟩
  have hProd : (h : SL(2, ℤ)) * g = g * t := by
    change (g * t * g⁻¹) * g = g * t
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hy : (h : SL(2, ℤ)) • (g • z) = g • (t • z) := by
    rw [← mul_smul, hProd, mul_smul]
  have hPhase : negativePhase (h : SL(2, ℤ)) (g • z) * negativePhase g z =
      negativePhase g (t • z) * negativePhase t z := by
    rw [← negativePhase_mul, ← negativePhase_mul, hProd]
  have hRatio : negativePhase (h : SL(2, ℤ)) (g • z) / negativePhase g (t • z) =
      negativePhase t z / negativePhase g z := by
    apply (div_eq_div_iff (negativePhase_ne_zero g (t • z)) (negativePhase_ne_zero g z)).2
    rw [hPhase, mul_comm]
  change F (g • (t • z) : ℍ) / negativePhase g (t • z) =
    (levelCharacter h : ℂ) * negativePhase t z * (F (g • z : ℍ) / negativePhase g z)
  rw [← hy, hF h]
  calc
    _ = (levelCharacter h : ℂ) * F (g • z : ℍ) *
        (negativePhase (h : SL(2, ℤ)) (g • z) / negativePhase g (t • z)) := by ring
    _ = _ := by rw [hRatio]; ring

theorem cuspZero_levelFour_floquet {F : ℂ → ℂ} (hF : OddMaassLaw F) (z : ℍ) :
    cuspOddProfile F ModularGroup.S (ModularGroup.T ^ (4 : ℤ) • z) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6) *
        cuspOddProfile F ModularGroup.S z := by
  have hm : ModularGroup.S * ModularGroup.T ^ (4 : ℤ) * ModularGroup.S⁻¹ ∈
      CongruenceSubgroup.Gamma0 4 := conjugatedTranslation_level 4 ModularGroup.S
  have hC : levelCharacter ⟨ModularGroup.S * ModularGroup.T ^ (4 : ℤ) * ModularGroup.S⁻¹, hm⟩ = 1 :=
    character_zero_translation 4
  rw [cuspOddProfile_shift hF _ _ hm, hC, Int.cast_one, one_mul, negativePhase_T_pow]
  congr 2
  push_cast
  ring

theorem oddInfinity_floquet {F : ℂ → ℂ} (hF : OddMaassLaw F) (z : ℍ) :
    F (ModularGroup.T • z : ℍ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 24) * F z := by
  let g : CongruenceSubgroup.Gamma0 4 :=
    ⟨ModularGroup.T, Paper8EtaLevelZeroMode.translation_mem_level 4⟩
  have hC : levelCharacter g = 1 := by
    rw [levelCharacter_apply]
    change chiFour ((ModularGroup.T 1 1 : ℤ) : ZMod 4) = 1
    have hT : ModularGroup.T 1 1 = (1 : ℤ) := by simp [ModularGroup.coe_T]
    rw [hT, Int.cast_one]
    decide
  have hP : negativePhase ModularGroup.T z =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 24) := by
    simpa only [zpow_one, Int.cast_one, mul_one] using negativePhase_T_pow 1 z
  simpa only [show (g : SL(2, ℤ)) = ModularGroup.T from rfl, hC, Int.cast_one, one_mul, hP]
    using hF g z

def normalizedZeroProfile (F : ℂ → ℂ) (x y : ℝ) : ℂ :=
  cuspOddProfile F ModularGroup.S (ofComplex (MaassLaplacian.complexPoint (4 * x) (4 * y)))

theorem normalizedZeroProfile_floquet {F : ℂ → ℂ} (hF : OddMaassLaw F) (x y : ℝ) (hy : 0 < y) :
    normalizedZeroProfile F (x + 1) y =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6) * normalizedZeroProfile F x y := by
  let w := MaassLaplacian.complexPoint (4 * x) (4 * y)
  let v := MaassLaplacian.complexPoint (4 * (x + 1)) (4 * y)
  have hw : 0 < w.im := by unfold w; rw [MaassLaplacian.complexPoint_im]; positivity
  have hv : 0 < v.im := by unfold v; rw [MaassLaplacian.complexPoint_im]; positivity
  have hPoint : ModularGroup.T ^ (4 : ℤ) • ofComplex w = ofComplex v := by
    rw [UpperHalfPlane.modular_T_zpow_smul, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hv]
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd]
    change ((4 : ℝ) : ℂ) + w = v
    unfold w v MaassLaplacian.complexPoint
    push_cast
    ring
  unfold normalizedZeroProfile
  change cuspOddProfile F ModularGroup.S (ofComplex v) =
    _ * cuspOddProfile F ModularGroup.S (ofComplex w)
  rw [← hPoint]
  exact cuspZero_levelFour_floquet hF (ofComplex w)

end
end ManuscriptAudit.Paper8OddCuspFloquetPhase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCuspFloquetPhase.normalizedZeroProfile_floquet
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
