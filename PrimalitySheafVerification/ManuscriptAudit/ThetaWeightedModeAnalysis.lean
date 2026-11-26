import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ThetaGlobalSection
import PrimalitySheafVerification.ManuscriptAudit.ThetaLevelTwoTiles

/-! The actual theta mode has finite square mass and satisfies the printed pointwise equation. -/

namespace ManuscriptAudit.ThetaWeightedModeAnalysis

open MeasureTheory ThetaGlobalSection ThetaLevelTwoTiles MaassLaplacian
open scoped UpperHalfPlane

noncomputable section

theorem thetaWeightedMode_coord (z : ℍ) :
    thetaWeightedMode z = weighted (1 / 4) jacobiTheta z.re z.im := by
  have h : complexPoint z.re z.im = (z : ℂ) := by
    apply Complex.ext <;> simp [complexPoint]
  rw [thetaWeightedMode, weighted, h]

theorem thetaWeightedMode_square_integrable_on_tiles :
    IntegrableOn (fun z : ℍ => ‖thetaWeightedMode z‖ ^ (2 : ℕ))
      tileCarrier (volume : Measure ℍ) := by
  simp only [thetaWeightedMode_norm_sq]
  exact levelTwo_tiles_integrable

theorem thetaWeightedMode_delta (z : ℍ) :
    maassDelta (1 / 2) (weighted (1 / 4) jacobiTheta) z.re z.im =
      (3 / 16 : ℂ) * thetaWeightedMode z := by
  rw [thetaWeightedMode_coord]
  exact jacobiTheta_delta_half z.re z.im z.im_pos

end
end ManuscriptAudit.ThetaWeightedModeAnalysis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaWeightedModeAnalysis.thetaWeightedMode_coord,
      ``ManuscriptAudit.ThetaWeightedModeAnalysis.thetaWeightedMode_square_integrable_on_tiles,
      ``ManuscriptAudit.ThetaWeightedModeAnalysis.thetaWeightedMode_delta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
