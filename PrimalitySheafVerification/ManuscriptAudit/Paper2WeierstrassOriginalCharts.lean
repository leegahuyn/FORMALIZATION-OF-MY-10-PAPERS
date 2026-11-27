import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassDerivativeOpen
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassProjectionSmooth

/-! The reversed presentation identifies the second étale chart with the same open on the original curve. -/

namespace ManuscriptAudit.Paper2WeierstrassOriginalCharts

open AlgebraicGeometry Polynomial WeierstrassCurve
open Paper2WeierstrassDerivativeOpen Paper2WeierstrassReverseProjection

noncomputable section

variable {R : Type*} [CommRing R]

/-- The second étale chart viewed as a localization of the original coordinate algebra. -/
def secondChartOriginal (W : WeierstrassCurve R) :
    Localization.Away (xDerivative W) ≃ₐ[R] ReverseProjectionChart W := by
  let f := polynomialInX W
  let b := AdjoinRoot.mk f f.derivative
  letI : IsLocalization.Away (-b) (ReverseProjectionChart W) := by
    have h := IsLocalization.Away.mul_of_isUnit (S := ReverseProjectionChart W)
      b (-1) (by simp)
    simpa only [mul_neg, mul_one] using h
  apply IsLocalization.algEquivOfAlgEquiv (Localization.Away (xDerivative W))
    (ReverseProjectionChart W) (swapPresentation W)
  change Submonoid.map (swapPresentation W).toRingEquiv (Submonoid.powers (xDerivative W)) =
    Submonoid.powers (-b)
  rw [Submonoid.map_powers]
  congr 1
  exact reversed_xDerivative W

private theorem polynomial_ring_smooth :
    (algebraMap R (Polynomial R)).Smooth :=
  (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    (Paper2WeierstrassProjectionSmooth.affineLine_smooth (R := R))

/-- The original first-derivative localization is a smooth algebra over the ground ring. -/
theorem xChart_smooth (W : WeierstrassCurve R) :
    Algebra.Smooth R (Localization.Away (xDerivative W)) := by
  have hEtale := projection_etale W
  letI := hEtale
  have hProjection : (algebraMap (Polynomial R) (ReverseProjectionChart W)).Smooth :=
    RingHom.smooth_algebraMap.mpr inferInstance
  have h : Algebra.Smooth R (ReverseProjectionChart W) := by
    apply RingHom.smooth_algebraMap.mp
    rw [IsScalarTower.algebraMap_eq R (Polynomial R) (ReverseProjectionChart W)]
    exact polynomial_ring_smooth.comp hProjection
  letI := h
  exact Algebra.Smooth.of_equiv (secondChartOriginal W).symm

/-- The original second-derivative localization is a smooth algebra over the ground ring. -/
theorem yChart_smooth (W : WeierstrassCurve R) :
    Algebra.Smooth R (Localization.Away (yDerivative W)) := by
  rw [← original_yDerivative]
  letI := Paper2WeierstrassEtaleProjection.projection_etale W
  have hProjection :
      (algebraMap (Polynomial R) (Paper2WeierstrassEtaleProjection.ProjectionChart W)).Smooth :=
    RingHom.smooth_algebraMap.mpr inferInstance
  apply RingHom.smooth_algebraMap.mp
  rw [IsScalarTower.algebraMap_eq R (Polynomial R) (Paper2WeierstrassEtaleProjection.ProjectionChart W)]
  exact polynomial_ring_smooth.comp hProjection

end
end ManuscriptAudit.Paper2WeierstrassOriginalCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassOriginalCharts.secondChartOriginal,
      ``ManuscriptAudit.Paper2WeierstrassOriginalCharts.xChart_smooth,
      ``ManuscriptAudit.Paper2WeierstrassOriginalCharts.yChart_smooth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
