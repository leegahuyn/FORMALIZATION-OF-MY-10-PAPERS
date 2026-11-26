import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSheafCohomology
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorSheaf
import PrimalitySheafVerification.ManuscriptAudit.EtaleFiniteSkyscraperCohomology
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleCoproduct
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleHOneDescent

/-!
# Vanishing degree-one cohomology of the affine-line divisor sheaf

The finite subfamilies are finite coproducts of actual geometric
skyscrapers, which are acyclic in positive degrees. Degree-one
descent from finite subfamilies gives the vanishing for the actual
finite-support divisor sheaf.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open IsDedekindDomain FiniteSupportPresheaf GeometricSkyscraperCohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := Polynomial K
private abbrev P := HeightOneSpectrum (A K)
private abbrev E := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
private abbrev Full := Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}

private abbrev x (p : P K) :=
  AffineLineRationalClosedPoints.rationalPoint K
    ((AffineLineRationalClosedPoints.closedPointEquiv K).symm p)

private abbrev fullPiece (p : P K) : Full K :=
  (Scheme.pointSmallEtale (x K p)).skyscraperSheaf (AddCommGrpCat.of ℤ)

private abbrev affinePiece (p : P K) := (E K).inverse.obj (fullPiece K p)

set_option maxHeartbeats 2200000 in
/-- Every chosen finite sum of the actual affine-line divisor pieces has zero H¹. -/
theorem finiteDivisor_HOne_subsingleton (t : Finset (P K)) :
    Subsingleton (Sheaf.H (affineEtaleDirectSum (X K) (fun p : t ↦ affinePiece K p.val)) 1) := by
  letI : IsGrothendieckAbelian.{0} (Full K) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology (X K) AddCommGrpCat.{0}
  let hCol : HasColimitsOfSize.{0, 0} (Full K) := IsGrothendieckAbelian.hasColimits _
  letI : HasColimitsOfShape (Discrete ↥t) (Full K) := hCol.has_colimits_of_shape _
  let D (p : t) := affinePiece K p.val
  let A := affineEtaleDirectSum (X K) D
  let H (p : t) := (E K).functor.obj (D p)
  let G (p : t) := fullPiece K p.val
  let h₁ := affineEtaleDirectSumIsColimit (X K) D
  let h₂ := isColimitCofanMkObjOfIsColimit (E K).functor D (summand (X K) D) h₁
  let e₀ : (E K).functor.obj A ≅ ∐ H := h₂.coconePointUniqueUpToIso (coproductIsCoproduct H)
  let e₁ : ∐ H ≅ ∐ G := Sigma.mapIso (fun p ↦ (E K).counitIso.app (G p))
  let e₂ := ((Sheaf.functorH (X K).smallEtaleTopology 1).mapIso
    (e₀ ≪≫ e₁)).addCommGroupIsoToAddEquiv
  let e := (SmallEtaleCohomologyComparison.sheafCohomologyEquiv
    (CommRingCat.of (Polynomial K)) A 1).trans e₂
  have hG : Subsingleton (Sheaf.H (∐ G) 1) :=
    finiteSkyscraperCoproduct_H_succ_subsingleton
      (fun p : t ↦ Scheme.pointSmallEtale (x K p.val)) (fun _ ↦ AddCommGrpCat.of ℤ) 0
  exact ⟨fun a b ↦ e.injective (hG.allEq (e a) (e b))⟩

/-- The finite-support divisor sheaf has zero H¹ on the affine site. -/
theorem affineDivisor_HOne_subsingleton : Subsingleton (Sheaf.H (affineDivisorSheaf K) 1) := by
  let R := CommRingCat.of (Polynomial K)
  exact affineEtaleDirectSum_HOne_subsingleton (X K) (affinePiece K)
    (KummerAffineCohomology.affineTerminal_isTerminal R) (finiteDivisor_HOne_subsingleton K)

/-- The actual affine-line divisor sheaf has zero H¹ on the full étale site. -/
theorem divisor_HOne_subsingleton : Subsingleton (Sheaf.H (divisorSheaf K) 1) := by
  let e := SmallEtaleCohomologyComparison.sheafCohomologyEquiv
    (CommRingCat.of (A K)) (affineDivisorSheaf K) 1
  have h := affineDivisor_HOne_subsingleton K
  exact ⟨fun a b ↦ e.symm.injective (h.allEq (e.symm a) (e.symm b))⟩

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.finiteDivisor_HOne_subsingleton,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisor_HOne_subsingleton,
      ``ManuscriptAudit.AffineLineDivisorSheaf.divisor_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
