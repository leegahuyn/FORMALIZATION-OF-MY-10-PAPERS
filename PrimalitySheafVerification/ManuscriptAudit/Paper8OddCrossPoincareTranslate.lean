import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareConvergence
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCuspFloquetPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8CrossCuspScalingWidths

/-! The exact right-cusp translation phase needed to unfold the first cross-cusp Fourier mode. -/

namespace ManuscriptAudit.Paper8OddCrossPoincareTranslate

open UpperHalfPlane MaassLaplacian Paper8OddCrossCuspNormalization
open Paper8OddCrossPoincareConvergence Paper8OddCrossPoincareHeight
open Paper8OddCrossPoincareKernel Paper8OddCrossScaledRows Paper8OddCrossCuspActualMultiplier
open Paper8OddCrossCuspRows Paper8CrossCuspScalingWidths Paper8OddCuspFloquetPhase
open Paper8EtaHalfWeightPhase Paper8EtaPhaseCocycle Paper8EtaPositiveLowerLeftMultiplier
open scoped MatrixGroups

noncomputable section

theorem translatePoint_coe (n : ℤ) (z : ℍ) :
    (translatePoint n z : ℂ) = (n : ℂ) + (z : ℂ) := by
  calc
    _ = (n : ℂ) + complexPoint z.re z.im := by
      change complexPoint ((n : ℝ) + z.re) z.im = _
      unfold complexPoint
      push_cast
      ring
    _ = _ := by rw [show complexPoint z.re z.im = (z : ℂ) from Complex.re_add_im z]

theorem translatePoint_re (n : ℤ) (z : ℍ) : (translatePoint n z).re = (n : ℝ) + z.re := by
  change ((translatePoint n z : ℍ) : ℂ).re = _
  rw [translatePoint_coe, Complex.add_re, Complex.intCast_re]
  rfl

theorem translatePoint_zero (z : ℍ) : translatePoint 0 z = z := by
  apply UpperHalfPlane.ext
  rw [translatePoint_coe, Int.cast_zero, zero_add]

theorem realDiagonalWidthFour_smul_coe (z : ℍ) :
    ((realDiagonalWidthFour • z : ℍ) : ℂ) = 4 * (z : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change (((2 : ℝ) : ℂ) * z + ((0 : ℝ) : ℂ)) /
    (((0 : ℝ) : ℂ) * z + ((1 / 2 : ℝ) : ℂ)) = _
  norm_num <;> ring

theorem realDiagonalWidthFour_translate (n : ℤ) (z : ℍ) :
    ModularGroup.T ^ (4 * n) • (realDiagonalWidthFour • z : ℍ) =
      realDiagonalWidthFour • translatePoint n z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    realDiagonalWidthFour_smul_coe, realDiagonalWidthFour_smul_coe, translatePoint_coe]
  push_cast
  ring

private theorem rightCuspStabilizer_mul_S (n : ℤ) :
    (rightCuspStabilizer n : SL(2, ℤ)) * ModularGroup.S = ModularGroup.S * ModularGroup.T ^ (4 * n) := by
  change (ModularGroup.S * ModularGroup.T ^ (4 * n) * ModularGroup.S⁻¹) * ModularGroup.S = _
  simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem scaledCross_translate_eq_orbit {D : ℕ} (A : CrossRow D) (n : ℤ) (z : ℍ) :
    scaledCrossMatrix A • translatePoint n z =
      ((crossGroupElement A * rightCuspStabilizer n : CongruenceSubgroup.Gamma0 4) : SL(2, ℤ)) •
        (ModularGroup.S • (realDiagonalWidthFour • z : ℍ)) := by
  have hMat : scaledCrossMatrix A = (A.matrix : SL(2, ℝ)) * realDiagonalWidthFour := by
    apply Subtype.ext
    exact scaledCrossMatrix_as_product A
  have hAction (v : ℍ) : (A.matrix : SL(2, ℝ)) • v = A.matrix • v := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
    rfl
  rw [hMat, mul_smul, hAction, ← realDiagonalWidthFour_translate n z,
    ← crossGroupElement_mul_S A, mul_smul]
  change (crossGroupElement A : SL(2, ℤ)) •
      (ModularGroup.S • (ModularGroup.T ^ (4 * n) • (realDiagonalWidthFour • z : ℍ))) =
    ((crossGroupElement A : SL(2, ℤ)) * (rightCuspStabilizer n : SL(2, ℤ))) •
      (ModularGroup.S • (realDiagonalWidthFour • z : ℍ))
  rw [mul_smul, ← mul_smul (rightCuspStabilizer n : SL(2, ℤ)),
    rightCuspStabilizer_mul_S, mul_smul]

private theorem rightCuspStabilizer_phase (n : ℤ) (q : ℍ) :
    oddEtaPhase (rightCuspStabilizer n) (ModularGroup.S • q) *
      negativeSquareRootPhase ModularGroup.S q =
      negativeSquareRootPhase ModularGroup.S (ModularGroup.T ^ (4 * n) • q) *
        negativePhase (ModularGroup.T ^ (4 * n)) q := by
  have hChar : levelCharacter (rightCuspStabilizer n) = 1 := by
    rw [levelCharacter_apply]
    exact character_zero_translation (4 * n)
  have hC : 0 < ModularGroup.S 1 0 := by norm_num [ModularGroup.coe_S]
  have h := congrArg (fun g : SL(2, ℤ) => negativePhase g q) (rightCuspStabilizer_mul_S n)
  simp only [negativePhase_mul] at h
  rw [negativePhase_principal ModularGroup.S hC q,
    negativePhase_principal ModularGroup.S hC (ModularGroup.T ^ (4 * n) • q)] at h
  have hNu : principalEtaMultiplier ModularGroup.S ≠ 0 := by
    intro h0
    have hp := principalEtaMultiplier_pow_twentyFour ModularGroup.S
    rw [h0, zero_pow (by decide : (24 : ℕ) ≠ 0)] at hp
    exact zero_ne_one hp
  rw [oddEtaPhase, hChar, Int.cast_one, one_mul]
  apply mul_left_cancel₀ hNu
  calc
    _ = negativePhase (rightCuspStabilizer n : SL(2, ℤ)) (ModularGroup.S • q) *
      (principalEtaMultiplier ModularGroup.S * negativeSquareRootPhase ModularGroup.S q) := by ring
    _ = _ := h.trans (by ring)

private theorem conjugate_right_translation (n : ℤ) (q : ℍ) :
    (starRingEnd ℂ) (negativePhase (ModularGroup.T ^ (4 * n)) q) =
      exponentialPhase (((-oddZeroFrequency * (n : ℝ)) : ℝ) : ℂ) := by
  rw [negativePhase_T_pow, ← Complex.exp_conj, exponentialPhase]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, map_intCast, Complex.conj_ofReal, Complex.conj_I,
    oddZeroFrequency]
  push_cast
  ring

theorem actualCrossPhase_zero {D : ℕ} (A : CrossRow (D + 1)) (z : ℍ) :
    actualCrossPhase z ⟨D, A, 0⟩ =
      (starRingEnd ℂ) (oddEtaPhase (crossGroupElement A) (ModularGroup.S • (realDiagonalWidthFour • z : ℍ))) *
        (starRingEnd ℂ) (negativeSquareRootPhase ModularGroup.S (realDiagonalWidthFour • z)) := by
  have h0 : rightCuspStabilizer 0 = 1 := by
    apply Subtype.ext
    change ModularGroup.S * ModularGroup.T ^ (4 * (0 : ℤ)) * ModularGroup.S⁻¹ = 1
    simp
  change (starRingEnd ℂ) (oddEtaPhase (crossGroupElement A * rightCuspStabilizer 0)
      (ModularGroup.S • (realDiagonalWidthFour • z : ℍ))) * _ = _
  rw [h0, mul_one]

theorem actualCrossPhase_translate {D : ℕ} (A : CrossRow (D + 1)) (n : ℤ) (z : ℍ) :
    actualCrossPhase z ⟨D, A, n⟩ =
      actualCrossPhase (translatePoint n z) ⟨D, A, 0⟩ *
        exponentialPhase (((-oddZeroFrequency * (n : ℝ)) : ℝ) : ℂ) := by
  let q : ℍ := realDiagonalWidthFour • z
  let t : SL(2, ℤ) := ModularGroup.T ^ (4 * n)
  have hAct : (rightCuspStabilizer n : SL(2, ℤ)) • (ModularGroup.S • q) =
      ModularGroup.S • (t • q) := by
    rw [← mul_smul, rightCuspStabilizer_mul_S, mul_smul]
  change (starRingEnd ℂ) (oddEtaPhase (crossGroupElement A * rightCuspStabilizer n) (ModularGroup.S • q)) *
    (starRingEnd ℂ) (negativeSquareRootPhase ModularGroup.S q) = _
  rw [oddEtaPhase_mul, hAct, map_mul, mul_assoc, ← map_mul, rightCuspStabilizer_phase, map_mul,
    conjugate_right_translation, actualCrossPhase_zero]
  rw [show t • q = realDiagonalWidthFour • translatePoint n z from realDiagonalWidthFour_translate n z]
  ring

def oddCrossFourierTerm (s : ℂ) (z : ℍ) (i : CrossIndex) : ℂ :=
  actualCrossPhase z i * oddCrossSeed s z i *
    exponentialPhase (((-oddZeroFrequency * z.re) : ℝ) : ℂ)

theorem oddCrossFourierTerm_translate {D : ℕ} (A : CrossRow (D + 1)) (n : ℤ) (s : ℂ) (z : ℍ) :
    oddCrossFourierTerm s z ⟨D, A, n⟩ =
      oddCrossFourierTerm s (translatePoint n z) ⟨D, A, 0⟩ := by
  have hSeed : oddCrossSeed s z ⟨D, A, n⟩ =
      oddCrossSeed s (translatePoint n z) ⟨D, A, 0⟩ := by
    unfold oddCrossSeed
    simp only [translatePoint_zero]
  have hExp : exponentialPhase (((-oddZeroFrequency * (n : ℝ)) : ℝ) : ℂ) *
      exponentialPhase (((-oddZeroFrequency * z.re) : ℝ) : ℂ) =
      exponentialPhase (((-oddZeroFrequency * (translatePoint n z).re) : ℝ) : ℂ) := by
    rw [exponentialPhase, exponentialPhase, exponentialPhase, ← Complex.exp_add, translatePoint_re]
    congr 1
    push_cast
    ring
  unfold oddCrossFourierTerm
  rw [actualCrossPhase_translate, hSeed]
  calc
    _ = actualCrossPhase (translatePoint n z) ⟨D, A, 0⟩ *
        oddCrossSeed s (translatePoint n z) ⟨D, A, 0⟩ * _ := by
          rw [← hExp]
          ring
    _ = _ := rfl

end
end ManuscriptAudit.Paper8OddCrossPoincareTranslate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossPoincareTranslate.oddCrossFourierTerm_translate
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
