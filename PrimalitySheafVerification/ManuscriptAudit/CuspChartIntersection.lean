import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProperYChart

/-!
# The intersection of the affine charts of the proper cusp

Pulling the affine cusp chart back to the second affine line gives the
principal open of its coordinate. Its spectrum is the Laurent line,
which is also the spectrum of the cusp algebra localized at its square
coordinate.
-/

namespace ManuscriptAudit.CuspChartIntersection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspPunctured CuspProperCompactification CuspProperYChart

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000

universe u

variable (K : Type u) [Field K]

/-- The Laurent line maps to the affine line by the polynomial inclusion. -/
def laurentToAffineLine :
    Spec (CommRingCat.of (LaurentPolynomial K)) ⟶ Spec (CommRingCat.of (Polynomial K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (LaurentPolynomial K)))

instance laurentToAffineLine_isOpenImmersion : IsOpenImmersion (laurentToAffineLine K) :=
  IsOpenImmersion.of_isLocalization (S := LaurentPolynomial K) (Polynomial.X : Polynomial K)

private theorem laurentToAffineLine_opensRange :
    (laurentToAffineLine K).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial K)
    (Polynomial.X : Polynomial K)

theorem overlap_snd_opensRange :
    (pullback.snd (affineOpen K) (lineOpen K)).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) := by
  rw [Scheme.Hom.opensRange_pullbackSnd, lineOpen_preimage_affine]

private theorem chartRanges_eq :
    Set.range (pullback.snd (affineOpen K) (lineOpen K)) =
      Set.range (laurentToAffineLine K) :=
  congrArg (fun U : (Spec (CommRingCat.of (Polynomial K))).Opens =>
    (U : Set (Spec (CommRingCat.of (Polynomial K)))))
    ((overlap_snd_opensRange K).trans (laurentToAffineLine_opensRange K).symm)

/-- The actual pullback of the two charts is the Laurent line. -/
def overlapIsoLaurent :
    pullback (affineOpen K) (lineOpen K) ≅ Spec (CommRingCat.of (LaurentPolynomial K)) :=
  IsOpenImmersion.isoOfRangeEq (pullback.snd (affineOpen K) (lineOpen K))
    (laurentToAffineLine K) (chartRanges_eq K)

@[reassoc]
theorem overlapIsoLaurent_hom_toAffineLine :
    (overlapIsoLaurent K).hom ≫ laurentToAffineLine K = pullback.snd (affineOpen K) (lineOpen K) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The same intersection in the coordinate ring of the punctured cusp. -/
def overlapIsoPuncturedCusp :
    pullback (affineOpen K) (lineOpen K) ≅
      Spec (CommRingCat.of (Localization.Away (cuspSquare K))) :=
  (overlapIsoLaurent K) ≪≫
    Scheme.Spec.mapIso (paper2_cusp_punctured_coordinate_equiv K).toRingEquiv.toCommRingCatIso.op

end

end ManuscriptAudit.CuspChartIntersection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspChartIntersection.laurentToAffineLine_isOpenImmersion,
      ``ManuscriptAudit.CuspChartIntersection.overlap_snd_opensRange,
      ``ManuscriptAudit.CuspChartIntersection.overlapIsoLaurent,
      ``ManuscriptAudit.CuspChartIntersection.overlapIsoLaurent_hom_toAffineLine,
      ``ManuscriptAudit.CuspChartIntersection.overlapIsoPuncturedCusp] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
