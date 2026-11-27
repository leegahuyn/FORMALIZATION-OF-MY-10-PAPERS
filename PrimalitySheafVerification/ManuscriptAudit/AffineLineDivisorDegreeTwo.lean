import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHOne
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleHTwoDescent

/-! Degree-two acyclicity of the actual affine-line divisor sheaf. -/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory
open IsDedekindDomain FiniteSupportPresheaf GeometricSkyscraperCohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev P := HeightOneSpectrum (Polynomial K)
private abbrev E := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
private abbrev Full := Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}

private abbrev x (p : P K) :=
  AffineLineRationalClosedPoints.rationalPoint K
    ((AffineLineRationalClosedPoints.closedPointEquiv K).symm p)

private abbrev fullPiece (p : P K) : Full K :=
  (Scheme.pointSmallEtale (x K p)).skyscraperSheaf (AddCommGrpCat.of ℤ)

private abbrev affinePiece (p : P K) := (E K).inverse.obj (fullPiece K p)

private theorem finiteDivisor_HTwo_subsingleton (t : Finset (P K)) :
    Subsingleton (Sheaf.H (affineEtaleDirectSum (X K) (fun p : t ↦ affinePiece K p.val)) 2) := by
  refine finiteDirectSum_H_subsingleton (X K) (fun p : t ↦ affinePiece K p.val) 2 ?_
  intro p
  let G : Full K := fullPiece K p.val
  let D := (E K).inverse.obj G
  let R := CommRingCat.of (Polynomial K)
  let H := Sheaf.functorH (X K).smallEtaleTopology 2
  let e₀ := SmallEtaleCohomologyComparison.sheafCohomologyEquiv R D 2
  let e₁ := (H.mapIso ((E K).counitIso.app G)).addCommGroupIsoToAddEquiv
  let e := e₀.trans e₁
  have h : Subsingleton (Sheaf.H G 2) :=
    geometricSkyscraperH_succ_subsingleton
      (Scheme.pointSmallEtale (x K p.val)) (AddCommGrpCat.of ℤ) 1
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

/-- The native finite-support divisor sheaf has zero H² on the affine site. -/
theorem affineDivisor_HTwo_subsingleton : Subsingleton (Sheaf.H (affineDivisorSheaf K) 2) := by
  let R := CommRingCat.of (Polynomial K)
  exact affineEtaleDirectSum_HTwo_subsingleton (X K) (affinePiece K)
    (KummerAffineCohomology.affineTerminal_isTerminal R) (finiteDivisor_HTwo_subsingleton K)

/-- The actual affine-line divisor sheaf has zero H² on the full étale site. -/
theorem divisor_HTwo_subsingleton : Subsingleton (Sheaf.H (divisorSheaf K) 2) := by
  let e := SmallEtaleCohomologyComparison.sheafCohomologyEquiv
    (CommRingCat.of (Polynomial K)) (affineDivisorSheaf K) 2
  have h := affineDivisor_HTwo_subsingleton K
  exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.divisor_HTwo_subsingleton
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
