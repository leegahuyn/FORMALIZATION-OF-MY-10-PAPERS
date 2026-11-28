import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaMaassEigenfunction
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspRows

/-! Native eta phase cocycles and the level-four odd cross-cusp multiplier. -/

namespace ManuscriptAudit.Paper8EtaPhaseCocycle

open UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8EtaHalfWeightPhase Paper8EtaMaassEigenfunction
open Paper8EtaPositiveLowerLeftMultiplier Paper8OddCrossCuspRows
open scoped MatrixGroups

noncomputable section

theorem positivePhase_mul (g h : SL(2, ℤ)) (z : ℍ) :
    positivePhase (g * h) z = positivePhase g (h • z) * positivePhase h z := by
  apply mul_right_cancel₀ (etaMaass_ne_zero z)
  calc
    _ = etaMaass ((g * h) • z) := (etaMaass_transform (g * h) z).symm
    _ = etaMaass (g • (h • z)) := by rw [mul_smul]
    _ = _ := by
      rw [etaMaass_transform g, etaMaass_transform h, mul_assoc]

theorem negativePhase_mul (g h : SL(2, ℤ)) (z : ℍ) :
    negativePhase (g * h) z = negativePhase g (h • z) * negativePhase h z := by
  simp only [negativePhase, positivePhase_mul, map_mul]

def oddEtaPhase (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) : ℂ :=
  (levelCharacter g : ℂ) * negativePhase (g : SL(2, ℤ)) z

theorem oddEtaPhase_mul (g h : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    oddEtaPhase (g * h) z =
      oddEtaPhase g ((h : SL(2, ℤ)) • z) * oddEtaPhase h z := by
  unfold oddEtaPhase
  rw [map_mul, Int.cast_mul]
  change (levelCharacter g : ℂ) * (levelCharacter h : ℂ) *
      negativePhase ((g : SL(2, ℤ)) * (h : SL(2, ℤ))) z = _
  rw [negativePhase_mul]
  ring

theorem positivePhase_principal (g : SL(2, ℤ)) (hg : 0 < g 1 0) (z : ℍ) :
    positivePhase g z =
      principalEtaMultiplier g *
        (Complex.sqrt (denominator g z) / (Real.sqrt ‖denominator g z‖ : ℂ)) := by
  have hEta : ModularForm.eta z ≠ 0 := ModularForm.eta_ne_zero z.im_pos
  have hSqrt : (Real.sqrt ‖denominator g z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))).ne'
  rw [positivePhase, eta_principal_transform g hg]
  field_simp [hEta, hSqrt] <;> ring

theorem negativePhase_principal (g : SL(2, ℤ)) (hg : 0 < g 1 0) (z : ℍ) :
    negativePhase g z =
      (starRingEnd ℂ) (principalEtaMultiplier g) *
        (starRingEnd ℂ) (Complex.sqrt (denominator g z) / (Real.sqrt ‖denominator g z‖ : ℂ)) := by
  simp only [negativePhase, positivePhase_principal g hg, map_mul]

theorem oddEtaPhase_cross (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    oddEtaPhase g (ModularGroup.S • z) =
      (levelCharacter g : ℂ) *
        (negativePhase ((g : SL(2, ℤ)) * ModularGroup.S) z / negativePhase ModularGroup.S z) := by
  have hNorm := negativePhase_norm ModularGroup.S z
  have hNe : negativePhase ModularGroup.S z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hNorm
    exact zero_ne_one hNorm
  rw [oddEtaPhase, negativePhase_mul, mul_div_cancel_right₀ _ hNe]

end
end ManuscriptAudit.Paper8EtaPhaseCocycle

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaPhaseCocycle.positivePhase_mul,
      ``ManuscriptAudit.Paper8EtaPhaseCocycle.oddEtaPhase_mul,
      ``ManuscriptAudit.Paper8EtaPhaseCocycle.oddEtaPhase_cross] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
