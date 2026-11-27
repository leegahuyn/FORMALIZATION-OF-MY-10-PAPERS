import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9OrthogonalCuspWaves

/-!
# A bounded cutoff remainder can fail weak lower semicontinuity

Physical PDF p. 480. The size estimate of A3.R alone permits this
bounded remainder on the actual quotient square-integrable cusp waves.
-/

namespace ManuscriptAudit.Paper10RemainderWeakLimit

open Filter ThetaChosenQuotientAnalysis GammaTwoQuotientHeightIntegral
open Paper9CuspWaveHilbert Paper9OrthogonalCuspWaves
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped Topology

noncomputable section

def boundedRemainder {E : Type*} [Norm E] (ε : ℝ) (x : E) : ℝ :=
  -ε * min (‖x‖^2) 1

theorem remainder_abs_le {E : Type*} [Norm E] {ε : ℝ} (hε : 0 ≤ ε) (x : E) :
    |boundedRemainder ε x| ≤ ε := by
  have hm : 0 ≤ min (‖x‖^2) (1 : ℝ) := le_min (sq_nonneg _) zero_le_one
  rw [boundedRemainder, abs_mul, abs_neg, abs_of_nonneg hε, abs_of_nonneg hm]
  exact mul_le_of_le_one_right hε (min_le_right _ _)

theorem absorbs_with_arbitrary_curvature (D : GammaTwoFundamentalDomain)
    {ε δ curvature : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hcurv : 0 ≤ curvature)
    (x : quotientL2 D) :
    |boundedRemainder ε x| ≤ δ * curvature + ε :=
  (remainder_abs_le hε x).trans (le_add_of_nonneg_left (mul_nonneg hδ hcurv))

theorem normalized_weak_limit_violates_lower_bound (D : GammaTwoFundamentalDomain)
    (k : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∀ x : quotientL2 D,
      Tendsto (fun n => inner ℂ (normalizedWave D k n) x) atTop (𝓝 0)) ∧
      (∀ n, boundedRemainder ε (normalizedWave D k n) = -ε) ∧
      -ε < boundedRemainder ε (0 : quotientL2 D) := by
  refine ⟨normalizedWave_inner_tendsto_zero D k, ?_, ?_⟩
  · intro n
    simp [boundedRemainder, normalizedWave_norm]
  · simpa [boundedRemainder] using (neg_lt_zero.mpr hε)

end
end ManuscriptAudit.Paper10RemainderWeakLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10RemainderWeakLimit.remainder_abs_le,
      ``ManuscriptAudit.Paper10RemainderWeakLimit.absorbs_with_arbitrary_curvature,
      ``ManuscriptAudit.Paper10RemainderWeakLimit.normalized_weak_limit_violates_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
