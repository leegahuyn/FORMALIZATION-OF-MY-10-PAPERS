import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoprimeTorusAlgebra
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCuspHOne

/-! Native schemes and ordinary étale cohomology for primitive torus binomials. -/

namespace ManuscriptAudit.CoprimeTorusEtale

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CoprimeTorusAlgebra

noncomputable section

universe u

variable (R : Type u) [CommRing R]

abbrev binomialCurve (m n : ℕ) : Scheme.{u} := Spec (CommRingCat.of (Curve R m n))
abbrev multiplicativeGroup : Scheme.{u} := Spec (CommRingCat.of (LaurentPolynomial R))

/-- The actual primitive binomial subscheme of the torus is a multiplicative group scheme as a scheme. -/
def curveIsoLaurent {m n : ℕ} (h : m.Coprime n) :
    binomialCurve R m n ≅ multiplicativeGroup R :=
  (Scheme.Spec.mapIso (coordinateEquiv R h).toRingEquiv.toCommRingCatIso.op).symm

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev group (d : ℕ) : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod d)

private abbrev puncturedCusp : Scheme.{0} :=
  Spec (CommRingCat.of (Localization.Away (CuspPunctured.cuspSquare K)))

private def puncturedToLaurent : multiplicativeGroup K ≅ puncturedCusp K :=
  Scheme.Spec.mapIso
    (CuspPunctured.paper2_cusp_punctured_coordinate_equiv K).toRingEquiv.toCommRingCatIso.op

/-- With prime-to-characteristic cyclic coefficients, the actual binomial curve has the Laurent-line H¹. -/
def cyclicHOneEquiv {m n : ℕ} (h : m.Coprime n) (d : ℕ)
    [NeZero (d : K)] (hd : 2 ≤ d) :
    ZMod d ≃+ Sheaf.H ((constantSheaf (binomialCurve K m n).smallEtaleTopology
      AddCommGrpCat.{0}).obj (group d)) 1 :=
  (SmallEtaleCuspHOne.puncturedCuspCyclicHOneEquiv K d hd).trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      ((curveIsoLaurent K h) ≪≫ puncturedToLaurent K).symm (group d) 1)

end
end ManuscriptAudit.CoprimeTorusEtale

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoprimeTorusEtale.curveIsoLaurent,
      ``ManuscriptAudit.CoprimeTorusEtale.cyclicHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
