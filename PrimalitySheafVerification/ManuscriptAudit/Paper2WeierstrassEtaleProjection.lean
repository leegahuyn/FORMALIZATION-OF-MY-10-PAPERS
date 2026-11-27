import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.StandardEtale

/-! The Weierstrass projection is étale on its actual derivative open. -/

namespace ManuscriptAudit.Paper2WeierstrassEtaleProjection

open Algebra WeierstrassCurve Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

private def standardPair (W : WeierstrassCurve R) : StandardEtalePair (Polynomial R) where
  f := W.toAffine.polynomial
  monic_f := Affine.monic_polynomial
  g := W.toAffine.polynomial.derivative
  cond := ⟨1, 0, 1, by simp⟩

/-- The derivative in the actual Weierstrass coordinate ring. -/
def yDerivative (W : WeierstrassCurve R) : W.toAffine.CoordinateRing :=
  AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomial.derivative

abbrev ProjectionChart (W : WeierstrassCurve R) :=
  Localization.Away (yDerivative W)

theorem projection_etale (W : WeierstrassCurve R) :
    Algebra.Etale (Polynomial R) (ProjectionChart W) := by
  exact Algebra.Etale.of_equiv (standardPair W).equivAwayAdjoinRoot

/-- On spectra, the genuine derivative chart maps étale to the first-coordinate affine line. -/
theorem projection_scheme_etale (W : WeierstrassCurve R) :
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap (Polynomial R) (ProjectionChart W)))) := by
  apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
  exact RingHom.etale_algebraMap.mpr (projection_etale W)

/-- Fixing the abscissa, the native derivative-open coordinate ring has unique square-zero lifts. -/
theorem projection_square_zero_unique (W : WeierstrassCurve R)
    (B : Type*) [CommRing B] [Algebra (Polynomial R) B]
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective ((Ideal.Quotient.mkₐ (Polynomial R) I).comp :
      (ProjectionChart W →ₐ[Polynomial R] B) → ProjectionChart W →ₐ[Polynomial R] B ⧸ I) := by
  letI := projection_etale W
  exact Algebra.FormallyEtale.comp_bijective (Polynomial R) (ProjectionChart W) I hI

end
end ManuscriptAudit.Paper2WeierstrassEtaleProjection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassEtaleProjection.projection_etale,
      ``ManuscriptAudit.Paper2WeierstrassEtaleProjection.projection_scheme_etale,
      ``ManuscriptAudit.Paper2WeierstrassEtaleProjection.projection_square_zero_unique] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
