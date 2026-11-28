import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassGaugeDerivative

/-! The exact eta-gauged Green current is invariant as a complex one-form. -/

namespace ManuscriptAudit.Paper8MaassGaugeCurrent

open UpperHalfPlane
open Paper8MaassEtaGauge Paper8MaassGaugeDerivative Paper8MaassWirtinger
open Paper8EtaCriticalOddVanishing Paper8EtaHalfWeightPhase Paper8ActualEtaSquaredModularity
open Paper8EtaInverseWeightedVanishing (levelCharacter_sq conjugate_squaredMultiplier_eq_inv)
open Paper8OddCrossCuspRows (levelCharacter)
open scoped MatrixGroups

noncomputable section

def gaugeSquare (z : ℍ) : ℝ := ‖etaGauge z‖ ^ 2

theorem gaugeSquare_invariant (g : SL(2, ℤ)) (z : ℍ) :
    gaugeSquare (g • z) = gaugeSquare z := by
  unfold gaugeSquare
  rw [etaGauge_transform, norm_mul, Complex.norm_conj, positivePhase_norm, one_mul]

def currentCoefficient (F : ℂ → ℂ) (z : ℍ) : ℂ :=
  (starRingEnd ℂ) (complexGaugeRatio F z) * (gaugeSquare z : ℂ) *
    derivativeZ (complexGaugeRatio F) z

private theorem oddGaugeCharacter_conj_mul (g : CongruenceSubgroup.Gamma0 4) :
    (starRingEnd ℂ) ((levelCharacter g : ℂ) * squaredMultiplier (g : SL(2, ℤ))) *
      ((levelCharacter g : ℂ) * squaredMultiplier (g : SL(2, ℤ))) = 1 := by
  let x : ℂ := levelCharacter g
  let y := squaredMultiplier (g : SL(2, ℤ))
  let c : ℂ →+* ℂ := starRingEnd ℂ
  have hx : c x * x = 1 := by
    simp only [c, x, map_intCast, ← pow_two, levelCharacter_sq]
  have hy : c y * y = 1 := by
    simp only [c, y, conjugate_squaredMultiplier_eq_inv, inv_mul_cancel₀, squaredMultiplier_ne_zero]
  change c (x * y) * (x * y) = 1
  calc
    _ = (c x * x) * (c y * y) := by rw [map_mul]; ring
    _ = _ := by rw [hx, hy, one_mul]

theorem currentCoefficient_pullback_eq {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    currentCoefficient F ((g : SL(2, ℤ)) • z) *
        deriv (fractionalLinear (g : SL(2, ℤ))) z = currentCoefficient F z := by
  let a := (g : SL(2, ℤ))
  let c : ℂ := (levelCharacter g : ℂ) * squaredMultiplier a
  have hc : (starRingEnd ℂ) c * c = 1 := oddGaugeCharacter_conj_mul g
  calc
    _ = ((starRingEnd ℂ) c * c) * currentCoefficient F z := by
      unfold currentCoefficient
      rw [gaugeSquare_invariant, gauge_derivativeZ_transform hLaw hF,
        (fractionalLinear_hasDerivAt a z).deriv, complexGaugeRatio_coe, gaugeRatio_transform hLaw,
        ← complexGaugeRatio_coe]
      simp only [c, a, map_mul]
      field_simp [denominator_ne_zero a z] <;> ring
    _ = _ := by rw [hc, one_mul]

end
end ManuscriptAudit.Paper8MaassGaugeCurrent

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassGaugeCurrent.currentCoefficient_pullback_eq
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
