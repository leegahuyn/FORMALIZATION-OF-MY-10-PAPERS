import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCriticalOddVanishing
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaMaassEigenfunction

/-! Gauge the odd negative half-weight Maass law to a constant character. -/

namespace ManuscriptAudit.Paper8MaassEtaGauge

open UpperHalfPlane
open Paper8EtaHalfWeightPhase Paper8EtaMaassEigenfunction Paper8EtaCriticalOddVanishing
open Paper8ActualEtaSquaredModularity
open Paper8OddCrossCuspRows (levelCharacter)
open MaassLaplacian Paper8NegativeHalfMaassFactorization
open scoped MatrixGroups

noncomputable section

def etaGauge (z : ℍ) : ℂ := (starRingEnd ℂ) (etaMaass z)

theorem etaGauge_ne_zero (z : ℍ) : etaGauge z ≠ 0 :=
  (map_ne_zero (starRingEnd ℂ)).2 (etaMaass_ne_zero z)

theorem etaGauge_transform (g : SL(2, ℤ)) (z : ℍ) :
    etaGauge (g • z) = (starRingEnd ℂ) (positivePhase g z) * etaGauge z := by
  simp only [etaGauge, etaMaass_transform, map_mul]

theorem negativePhase_mul_positivePhase (g : SL(2, ℤ)) (z : ℍ) :
    negativePhase g z * positivePhase g z = squaredMultiplier g := by
  have hD := denominator_ne_zero g z
  have hN : (‖denominator g z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hD)
  calc
    _ = positivePhase g z ^ 2 * ((‖denominator g z‖ : ℂ) / denominator g z) := by
      unfold negativePhase
      ring
    _ = _ := by
      rw [positivePhase_sq]
      field_simp [hD, hN] <;> ring

theorem negativePhase_div_conj_positivePhase (g : SL(2, ℤ)) (z : ℍ) :
    negativePhase g z / (starRingEnd ℂ) (positivePhase g z) = squaredMultiplier g := by
  have hNorm : positivePhase g z * (starRingEnd ℂ) (positivePhase g z) = 1 := by
    simpa only [positivePhase_norm, one_pow, Complex.ofReal_one] using
      Complex.mul_conj' (positivePhase g z)
  have hPh : positivePhase g z ≠ 0 := norm_ne_zero_iff.mp (by simp [positivePhase_norm])
  apply (div_eq_iff ((map_ne_zero (starRingEnd ℂ)).2 hPh)).2
  calc
    _ = (negativePhase g z * positivePhase g z) * (starRingEnd ℂ) (positivePhase g z) := by
      rw [mul_assoc, hNorm, mul_one]
    _ = _ := by rw [negativePhase_mul_positivePhase]

def gaugeRatio (F : ℂ → ℂ) (z : ℍ) : ℂ := F z / etaGauge z

theorem gaugeRatio_transform {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (g : CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    gaugeRatio F ((g : SL(2, ℤ)) • z) =
      (levelCharacter g : ℂ) * squaredMultiplier (g : SL(2, ℤ)) * gaugeRatio F z := by
  let a := (g : SL(2, ℤ))
  have h : (starRingEnd ℂ) (positivePhase a z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 (norm_ne_zero_iff.mp (by simp [positivePhase_norm]))
  calc
    _ = (levelCharacter g : ℂ) *
        (negativePhase a z / (starRingEnd ℂ) (positivePhase a z)) * gaugeRatio F z := by
      unfold gaugeRatio
      rw [hLaw g z, etaGauge_transform]
      dsimp only [a] at h ⊢
      field_simp [etaGauge_ne_zero z, h] <;> ring
    _ = _ := by rw [negativePhase_div_conj_positivePhase]

def raisingDerivative (B : Profile) (x y : ℝ) : ℂ :=
  Complex.I * (y : ℂ) * partialX B x y + (y : ℂ) * partialY B x y

theorem raising_mul (A B : Profile) (x y : ℝ)
    (hAx : DifferentiableAt ℝ (fun t => A t y) x) (hAy : DifferentiableAt ℝ (A x) y)
    (hBx : DifferentiableAt ℝ (fun t => B t y) x) (hBy : DifferentiableAt ℝ (B x) y) :
    raising (fun s t => A s t * B s t) x y =
      B x y * raising A x y + A x y * raisingDerivative B x y := by
  have hX :
      partialX (fun s t => A s t * B s t) x y =
        partialX A x y * B x y + A x y * partialX B x y := by
    have hFun : (fun t => A t y * B t y) = (fun t => A t y) * (fun t => B t y) := by
      funext t
      rfl
    unfold partialX
    rw [hFun]
    exact (hAx.hasDerivAt.mul hBx.hasDerivAt).deriv
  have hY :
      partialY (fun s t => A s t * B s t) x y =
        partialY A x y * B x y + A x y * partialY B x y := by
    have hFun : (fun t => A x t * B x t) = A x * B x := by
      funext t
      rfl
    unfold partialY
    rw [hFun]
    exact (hAy.hasDerivAt.mul hBy.hasDerivAt).deriv
  simp only [raising, hX, hY, raisingDerivative]
  ring

end
end ManuscriptAudit.Paper8MaassEtaGauge

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassEtaGauge.negativePhase_div_conj_positivePhase,
      ``ManuscriptAudit.Paper8MaassEtaGauge.gaugeRatio_transform,
      ``ManuscriptAudit.Paper8MaassEtaGauge.raising_mul] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
