import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import PrimalitySheafVerification.ManuscriptAudit.AffineLineRationalClosedPoints
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleSheaf

/-!
# The finite-support skyscraper sheaf on the affine line

On the small affine étale site sections have finite support among the
rational closed points. The native affine-to-full sheaf equivalence
gives a sheaf on the full small étale site.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory IsDedekindDomain

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]

/-- The actual affine line over `K`. -/
abbrev X := Spec (CommRingCat.of (Polynomial K))

private abbrev comparison := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}

/-- The native integer skyscraper at an actual rational closed point. -/
abbrev skyscraper (a : K) : Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0} :=
  (Scheme.pointSmallEtale (AffineLineRationalClosedPoints.rationalPoint K a)).skyscraperSheaf
    (AddCommGrpCat.of ℤ)

/-- The finite-support family of the rational-point skyscrapers on the
actual small affine étale site. -/
def affineDivisorSheaf : Sheaf (Scheme.AffineEtale.topology (X K)) AddCommGrpCat.{0} :=
  FiniteSupportPresheaf.affineEtaleDirectSum (X K)
    (fun p : HeightOneSpectrum (Polynomial K) ↦
      (comparison K).inverse.obj (skyscraper K
        ((AffineLineRationalClosedPoints.closedPointEquiv K).symm p)))

/-- The divisor sheaf on the full small étale site. -/
def divisorSheaf : Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0} :=
  (comparison K).functor.obj (affineDivisorSheaf K)

/-- Restriction of the full divisor sheaf gives the stated finite-support
affine étale sheaf. -/
def restrictionIso :
    (comparison K).inverse.obj (divisorSheaf K) ≅ affineDivisorSheaf K :=
  ((comparison K).unitIso.app (affineDivisorSheaf K)).symm

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.divisorSheaf,
      ``ManuscriptAudit.AffineLineDivisorSheaf.restrictionIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
