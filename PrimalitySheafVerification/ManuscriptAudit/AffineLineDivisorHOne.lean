import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSheafCohomology
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorSheaf
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleCohomology
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

set_option maxHeartbeats 700000 in
/-- Every chosen finite sum of the actual affine-line divisor pieces has zero H¹. -/
theorem finiteDivisor_HOne_subsingleton (t : Finset (P K)) :
    Subsingleton (Sheaf.H (affineEtaleDirectSum (X K) (fun p : t ↦ affinePiece K p.val)) 1) := by
  refine finiteDirectSum_H_subsingleton (X K) (fun p : t ↦ affinePiece K p.val) 1 ?_
  intro p
  let G : Full K := fullPiece K p.val
  let D := (E K).inverse.obj G
  let R := CommRingCat.of (Polynomial K)
  let H := Sheaf.functorH (X K).smallEtaleTopology 1
  let e₀ := SmallEtaleCohomologyComparison.sheafCohomologyEquiv R D 1
  let e₁ := (H.mapIso ((E K).counitIso.app G)).addCommGroupIsoToAddEquiv
  let e := e₀.trans e₁
  have h : Subsingleton (Sheaf.H G 1) :=
    geometricSkyscraperH_succ_subsingleton
      (Scheme.pointSmallEtale (x K p.val)) (AddCommGrpCat.of ℤ) 0
  exact ⟨fun a b ↦ e.injective (h.allEq (e a) (e b))⟩

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
