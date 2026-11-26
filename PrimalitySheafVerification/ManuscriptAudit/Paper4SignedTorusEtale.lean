import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import PrimalitySheafVerification.ManuscriptAudit.CoprimeTorusEtale
import PrimalitySheafVerification.ManuscriptAudit.Paper4SignedTorus

/-!
# The literal signed torus curves and their geometric étale H¹

Transport the primitive binomial calculation through the actual sign
and inversion of the Laurent coordinates in physical page 124.
-/

namespace ManuscriptAudit.Paper4SignedTorusEtale

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open Paper4SignedTorus

noncomputable section

universe u

variable (R : Type u) [CommRing R]

abbrev literalCurve (negative : Bool) (p A : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (PrintedCurve R negative p A))

/-- The actual signed subscheme and the primitive torus binomial
scheme are isomorphic. -/
def literalCurveIsoBinomial {p : ℕ} (hp : Odd p) (negative : Bool) (A : ℕ) :
    literalCurve R negative p A ≅ CoprimeTorusEtale.binomialCurve R p A :=
  (Scheme.Spec.mapIso
    (literalToBinomialEquiv R hp negative A).toRingEquiv.toCommRingCatIso.op).symm

def literalCurveIsoLaurent {p A : ℕ} (hp : Odd p) (hc : p.Coprime A) (negative : Bool) :
    literalCurve R negative p A ≅ CoprimeTorusEtale.multiplicativeGroup R :=
  (literalCurveIsoBinomial R hp negative A) ≪≫ CoprimeTorusEtale.curveIsoLaurent R hc

/-- The precise residue-field scheme of either sign in (F2). -/
def paper4_literalCurveIsoLaurent {p A : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p)
    (hA : A = 4 ∨ A = 3 ∨ A = 2) (negative : Bool) :
    literalCurve (ZMod p) negative p A ≅ CoprimeTorusEtale.multiplicativeGroup (ZMod p) :=
  (Scheme.Spec.mapIso
    (paper4_literal_coordinateEquiv hp h5 hA negative).toRingEquiv.toCommRingCatIso.op).symm

private theorem laurent_smooth : Algebra.Smooth R (LaurentPolynomial R) := by
  let e : Polynomial R →ₐ[R] LaurentPolynomial R := Polynomial.toLaurentAlg
  letI : IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
    IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  letI : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
  letI : Algebra.Smooth (Polynomial R) (LaurentPolynomial R) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial R)
  exact Algebra.Smooth.comp R (Polynomial R) (LaurentPolynomial R)

/-- The actual signed coordinate ring is smooth over its coefficient ring. -/
theorem literalAlgebra_smooth {p A : ℕ} (hp : Odd p) (hc : p.Coprime A)
    (negative : Bool) : Algebra.Smooth R (PrintedCurve R negative p A) := by
  letI := laurent_smooth R
  exact Algebra.Smooth.of_equiv (literalLaurentEquiv R hp hc negative).symm

def literalStructureMap (negative : Bool) (p A : ℕ) :
    literalCurve R negative p A ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (PrintedCurve R negative p A)))

/-- Smoothness of the actual affine structure morphism over the given base. -/
theorem literalStructureMap_smooth {p A : ℕ} (hp : Odd p) (hc : p.Coprime A)
    (negative : Bool) : AlgebraicGeometry.Smooth (literalStructureMap R negative p A) := by
  rw [literalStructureMap, HasRingHomProperty.Spec_iff]
  exact RingHom.smooth_algebraMap.mpr (literalAlgebra_smooth R hp hc negative)

theorem paper4_literalAlgebra_smooth {p A : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p)
    (hA : A = 4 ∨ A = 3 ∨ A = 2) (negative : Bool) :
    Algebra.Smooth (ZMod p) (PrintedCurve (ZMod p) negative p A) := by
  letI := laurent_smooth (ZMod p)
  exact Algebra.Smooth.of_equiv (paper4_literal_coordinateEquiv hp h5 hA negative).symm

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev coeff (d : ℕ) : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod d)

/-- Absolute geometric degree-one cohomology with prime-to-characteristic
cyclic coefficients, for either sign of the actual torus equation. -/
def literalCyclicHOneEquiv {p A : ℕ} (hp : Odd p) (hc : p.Coprime A) (negative : Bool)
    (d : ℕ) [NeZero (d : K)] (hd : 2 ≤ d) :
    ZMod d ≃+ Sheaf.H ((constantSheaf (literalCurve K negative p A).smallEtaleTopology
      AddCommGrpCat.{0}).obj (coeff d)) 1 :=
  (CoprimeTorusEtale.cyclicHOneEquiv K hc d hd).trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      (literalCurveIsoBinomial K hp negative A).symm (coeff d) 1)

end

end ManuscriptAudit.Paper4SignedTorusEtale

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper4SignedTorusEtale.literalCurveIsoBinomial,
      ``ManuscriptAudit.Paper4SignedTorusEtale.literalCurveIsoLaurent,
      ``ManuscriptAudit.Paper4SignedTorusEtale.paper4_literalCurveIsoLaurent,
      ``ManuscriptAudit.Paper4SignedTorusEtale.literalAlgebra_smooth,
      ``ManuscriptAudit.Paper4SignedTorusEtale.literalStructureMap_smooth,
      ``ManuscriptAudit.Paper4SignedTorusEtale.paper4_literalAlgebra_smooth,
      ``ManuscriptAudit.Paper4SignedTorusEtale.literalCyclicHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
