import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothMobiusGm
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartImmersion

/-! The actual Y-chart of the proper node is the second principal
open u≠−1 of the multiplicative group after the Möbius coordinate. -/

namespace ManuscriptAudit.NodalSmoothMobiusY

open AlgebraicGeometry CategoryTheory Polynomial
open NodalSmoothMobius (tDenominator tRing uDenominator uRing mobiusEquiv)
open NodalSmoothMobiusGm (laurentRing Gm)
open NodalYChartImmersion (yCoordinateRing coordinateEquiv nodeYChart)

noncomputable section

universe u
variable (K : Type u) [Field K]

private abbrev yLocalized := Localization.Away ((1 : Polynomial K) - Polynomial.X ^ 2)

private theorem squareDenominators_associated :
    Associated ((1 : Polynomial K) - Polynomial.X ^ 2) (tDenominator K) := by
  refine ⟨-1, ?_⟩
  change ((1 : Polynomial K) - Polynomial.X ^ 2) * (-1) = Polynomial.X ^ 2 - 1
  ring

private instance : IsLocalization.Away (tDenominator K) (yLocalized K) :=
  IsLocalization.Away.of_associated (S := yLocalized K) (squareDenominators_associated K)

private def yToT : yCoordinateRing K ≃ₐ[Polynomial K] tRing K :=
  (coordinateEquiv K).trans
    (IsLocalization.algEquiv (Submonoid.powers (tDenominator K)) (yLocalized K) (tRing K))

private def negatePolynomial : Polynomial K ≃ₐ[K] Polynomial K := by
  let f : Polynomial K →ₐ[K] Polynomial K := Polynomial.aeval (-Polynomial.X)
  have h : f.comp f = AlgHom.id K (Polynomial K) := by
    apply Polynomial.algHom_ext
    have hX : f (Polynomial.X : Polynomial K) = -Polynomial.X := Polynomial.aeval_X _
    change f (f Polynomial.X) = Polynomial.X
    rw [hX, map_neg, hX, neg_neg]
  exact AlgEquiv.ofAlgHom f f h h

private theorem negatePolynomial_X :
    negatePolynomial K (Polynomial.X : Polynomial K) = -Polynomial.X :=
  Polynomial.aeval_X _

def uPlusDenominator : Polynomial K := Polynomial.X * (Polynomial.X + 1)
abbrev uPlusRing := Localization.Away (uPlusDenominator K)

private theorem negatePolynomial_denominator :
    negatePolynomial K (uDenominator K) = uPlusDenominator K := by
  unfold uDenominator uPlusDenominator
  rw [map_mul, map_sub, map_one, negatePolynomial_X]
  ring

private def signedCoordinateEquiv : uRing K ≃ₐ[K] uPlusRing K :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (uDenominator K)) (T := Submonoid.powers (uPlusDenominator K))
    (uRing K) (uPlusRing K) (negatePolynomial K)
    (by rw [Submonoid.map_powers, negatePolynomial_denominator])

/-- Change coordinates from s=X/Y to u=(1−s)/(1+s). -/
def yMobiusEquiv (h2 : (2 : K) ≠ 0) : yCoordinateRing K ≃ₐ[K] uPlusRing K :=
  ((yToT K).restrictScalars K).trans ((mobiusEquiv K h2).trans (signedCoordinateEquiv K))

def uPlusOne : laurentRing K :=
  algebraMap (Polynomial K) (laurentRing K) (Polynomial.X + 1)

theorem uPlusOne_laurent :
    uPlusOne K = (LaurentPolynomial.T 1 : laurentRing K) + 1 := by
  rw [uPlusOne, LaurentPolynomial.algebraMap_eq_toLaurent, map_add, Polynomial.toLaurent_X,
    map_one]

abbrev plusRing := Localization.Away (uPlusOne K)

private instance : IsLocalization.Away (uPlusDenominator K) (plusRing K) :=
  IsLocalization.Away.mul' (laurentRing K) (plusRing K)
    (Polynomial.X : Polynomial K) (Polynomial.X + 1)

private def localizationEquiv : uPlusRing K ≃ₐ[Polynomial K] plusRing K :=
  IsLocalization.algEquiv (Submonoid.powers (uPlusDenominator K)) (uPlusRing K) (plusRing K)

/-- The multiplicative-group open in which u+1 is invertible. -/
def plusOpen : (Gm K).Opens := PrimeSpectrum.basicOpen (uPlusOne K)

private def plusInGm : Spec (CommRingCat.of (plusRing K)) ⟶ Gm K :=
  Spec.map (CommRingCat.ofHom (algebraMap (laurentRing K) (plusRing K)))

private instance : IsOpenImmersion (plusInGm K) :=
  IsOpenImmersion.of_isLocalization (S := plusRing K) (uPlusOne K)

private def localizationOpenIso : Spec (CommRingCat.of (plusRing K)) ≅ (plusOpen K).toScheme :=
  IsOpenImmersion.isoOfRangeEq (plusInGm K) (plusOpen K).ι (by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range (plusRing K) (uPlusOne K))

/-- The genuine nodal Y-chart is the multiplicative-group open D(u+1). -/
def nodalYIsoPlusOpen (h2 : (2 : K) ≠ 0) : nodeYChart K ≅ (plusOpen K).toScheme :=
  (Scheme.Spec.mapIso (yMobiusEquiv K h2).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (Scheme.Spec.mapIso (localizationEquiv K).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    localizationOpenIso K

end
end ManuscriptAudit.NodalSmoothMobiusY

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothMobiusY.yMobiusEquiv,
      ``ManuscriptAudit.NodalSmoothMobiusY.nodalYIsoPlusOpen] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
