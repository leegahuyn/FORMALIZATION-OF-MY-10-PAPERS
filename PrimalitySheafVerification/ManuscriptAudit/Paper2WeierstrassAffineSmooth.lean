import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassOriginalCharts
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassSpectrumCover

/-! Smoothness of the full affine elliptic Weierstrass scheme follows from its two native charts. -/

namespace ManuscriptAudit.Paper2WeierstrassAffineSmooth

open AlgebraicGeometry WeierstrassCurve Paper2WeierstrassDerivativeOpen
open Paper2WeierstrassOriginalCharts Paper2WeierstrassSpectrumCover

noncomputable section

variable {R : Type*} [CommRing R]

theorem partial_derivatives_span (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span ({xDerivative W, yDerivative W} : Set W.toAffine.CoordinateRing) = ⊤ := by
  by_contra hn
  obtain ⟨M, hM, hspan⟩ := Ideal.exists_le_maximal _ hn
  let P : PrimeSpectrum W.toAffine.CoordinateRing := ⟨M, hM.isPrime⟩
  have hx : xDerivative W ∈ P.asIdeal :=
    hspan (Ideal.subset_span (by simp))
  have hy : yDerivative W ∈ P.asIdeal :=
    hspan (Ideal.subset_span (by simp))
  have hCover : P ∈ (PrimeSpectrum.basicOpen (xDerivative W) :
      Set (PrimeSpectrum W.toAffine.CoordinateRing)) ∪ PrimeSpectrum.basicOpen (yDerivative W) := by
    rw [derivative_opens_cover W]
    exact Set.mem_univ P
  rcases hCover with hx' | hy'
  · exact (PrimeSpectrum.mem_basicOpen _ _).mp hx' hx
  · exact (PrimeSpectrum.mem_basicOpen _ _).mp hy' hy

theorem coordinate_ring_smooth (W : WeierstrassCurve R) [W.IsElliptic] :
    Algebra.Smooth R W.toAffine.CoordinateRing := by
  let A := W.toAffine.CoordinateRing
  let s : Set A := {xDerivative W, yDerivative W}
  apply RingHom.smooth_algebraMap.mp
  refine RingHom.Smooth.ofLocalizationSpanTarget (algebraMap R A) s
    (partial_derivatives_span W) ?_
  rintro ⟨r, hr⟩
  have h : r = xDerivative W ∨ r = yDerivative W := by simpa [s] using hr
  rcases h with rfl | rfl
  · rw [← IsScalarTower.algebraMap_eq R A (Localization.Away (xDerivative W))]
    exact RingHom.smooth_algebraMap.mpr (xChart_smooth W)
  · rw [← IsScalarTower.algebraMap_eq R A (Localization.Away (yDerivative W))]
    exact RingHom.smooth_algebraMap.mpr (yChart_smooth W)

theorem structural_map_smooth (W : WeierstrassCurve R) [W.IsElliptic] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing))) := by
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (coordinate_ring_smooth W))

end
end ManuscriptAudit.Paper2WeierstrassAffineSmooth

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassAffineSmooth.partial_derivatives_span,
      ``ManuscriptAudit.Paper2WeierstrassAffineSmooth.coordinate_ring_smooth,
      ``ManuscriptAudit.Paper2WeierstrassAffineSmooth.structural_map_smooth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
