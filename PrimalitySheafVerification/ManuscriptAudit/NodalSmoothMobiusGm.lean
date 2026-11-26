import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothMobius
import PrimalitySheafVerification.ManuscriptAudit.NodalAwayNormalization

/-! The actual punctured affine nodal chart is the principal open
u≠1 of the native multiplicative group. -/

namespace ManuscriptAudit.NodalSmoothMobiusGm

open AlgebraicGeometry CategoryTheory Polynomial
open NodalSmoothMobius (tRing uRing uDenominator mobiusEquiv)
open NodalAwayNormalization (nodeX normalizationEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

abbrev laurentRing := LaurentPolynomial K
abbrev Gm : Scheme.{u} := Spec (CommRingCat.of (laurentRing K))

def uMinusOne : laurentRing K :=
  algebraMap (Polynomial K) (laurentRing K) (Polynomial.X - 1)

theorem uMinusOne_laurent :
    uMinusOne K = (LaurentPolynomial.T 1 : laurentRing K) - 1 := by
  rw [uMinusOne, LaurentPolynomial.algebraMap_eq_toLaurent, map_sub, Polynomial.toLaurent_X,
    map_one]

abbrev minusRing := Localization.Away (uMinusOne K)

private instance : IsLocalization.Away (uDenominator K) (minusRing K) :=
  IsLocalization.Away.mul' (laurentRing K) (minusRing K)
    (Polynomial.X : Polynomial K) (Polynomial.X - 1)

private def localizationEquiv : uRing K ≃ₐ[Polynomial K] minusRing K :=
  IsLocalization.algEquiv (Submonoid.powers (uDenominator K)) (uRing K) (minusRing K)

/-- The multiplicative-group open in which u−1 is invertible. -/
def minusOpen : (Gm K).Opens := PrimeSpectrum.basicOpen (uMinusOne K)

private def minusInGm : Spec (CommRingCat.of (minusRing K)) ⟶ Gm K :=
  Spec.map (CommRingCat.ofHom (algebraMap (laurentRing K) (minusRing K)))

private instance : IsOpenImmersion (minusInGm K) :=
  IsOpenImmersion.of_isLocalization (S := minusRing K) (uMinusOne K)

private def localizationOpenIso : Spec (CommRingCat.of (minusRing K)) ≅ (minusOpen K).toScheme :=
  IsOpenImmersion.isoOfRangeEq (minusInGm K) (minusOpen K).ι (by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range (minusRing K) (uMinusOne K))

/-- The genuine affine nodal D(x) is the native multiplicative-group open D(u−1). -/
def nodalPunctureIsoMinusOpen (h2 : (2 : K) ≠ 0) :
    Spec (CommRingCat.of (Localization.Away (nodeX K))) ≅ (minusOpen K).toScheme :=
  (Scheme.Spec.mapIso (normalizationEquiv K).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (Scheme.Spec.mapIso (mobiusEquiv K h2).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (Scheme.Spec.mapIso (localizationEquiv K).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    localizationOpenIso K

end
end ManuscriptAudit.NodalSmoothMobiusGm

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalSmoothMobiusGm.nodalPunctureIsoMinusOpen
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
