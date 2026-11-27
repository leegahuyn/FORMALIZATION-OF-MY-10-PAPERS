import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCechSkyscrapers
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHOne

/-! The genuine affine-line divisor sheaf has zero positive étale cohomology. -/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineEtaleCechSkyscrapers EtaleCechDirectSum EtaleCechSectionLifts
open EtaleCechOrdinaryAcyclic FiniteSupportPresheaf IsDedekindDomain

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev R := CommRingCat.of (Polynomial K)
private abbrev G := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
private abbrev index := HeightOneSpectrum (Polynomial K)
private abbrev point (p : index K) :=
  Scheme.pointSmallEtale (AffineLineRationalClosedPoints.rationalPoint K
    ((AffineLineRationalClosedPoints.closedPointEquiv K).symm p))
private abbrev piece (p : index K) := (G K).inverse.obj ((point K p).skyscraperSheaf
  (AddCommGrpCat.of ℤ))

local instance : HasFiniteLimits (X K).AffineEtale := AffineEtaleMorphism.spec_hasFiniteLimits (R K)

/-- The actual divisor sheaf is Čech-acyclic on the affine étale site. -/
theorem affineDivisor_cechAcyclic : AffineCechAcyclic (affineDivisorSheaf K) := by
  intro U T f hf n
  change (Cech f (directSum fun p ↦ (piece K p).obj)).ExactAt (n + 1)
  exact directSum_exactAt_succ f (fun p ↦ (piece K p).obj) n (fun p ↦
    skyscraper_restriction_cechAcyclic (R K) (point K p) (AddCommGrpCat.of ℤ) f hf n)

/-- The actual affine-site divisor sheaf has no positive ordinary cohomology. -/
theorem affineDivisor_H_succ_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (affineDivisorSheaf K) (n + 1)) :=
  affine_H_succ_subsingleton (KummerAffineCohomology.affineTerminal_isTerminal (R K))
    (fun A _ ↦ exists_cechAcyclic_injectivePresentation (R K) A)
    n (affineDivisorSheaf K) (affineDivisor_cechAcyclic K)

/-- All positive ordinary small étale cohomology of the actual affine-line
divisor sheaf vanishes. -/
theorem divisor_H_succ_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (divisorSheaf K) (n + 1)) := by
  let e := SmallEtaleCohomologyComparison.sheafCohomologyEquiv (R K) (affineDivisorSheaf K) (n + 1)
  have h := affineDivisor_H_succ_subsingleton K n
  exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisor_cechAcyclic,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisor_H_succ_subsingleton,
      ``ManuscriptAudit.AffineLineDivisorSheaf.divisor_H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
