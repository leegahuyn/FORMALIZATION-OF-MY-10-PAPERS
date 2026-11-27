import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHOne
import PrimalitySheafVerification.ManuscriptAudit.AffineLineOpenDivisorSum
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSkyscraperRestriction

/-! Degree-one acyclicity of the actual affine-line divisor sheaf
restricted to an affine open. -/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleObjectRestriction FiniteSupportPresheaf IsDedekindDomain

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]
variable (R : CommRingCat.{0}) (j : Spec R ⟶ X K) [IsOpenImmersion j]

private abbrev P := HeightOneSpectrum (Polynomial K)
private abbrev V := Spec R
private abbrev E := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
private abbrev EV := Scheme.AffineEtale.sheafEquiv (V R) AddCommGrpCat.{0}

private abbrev x (p : P K) :=
  AffineLineRationalClosedPoints.rationalPoint K
    ((AffineLineRationalClosedPoints.closedPointEquiv K).symm p)

private abbrev fullPiece (p : P K) :=
  (Scheme.pointSmallEtale (x K p)).skyscraperSheaf (AddCommGrpCat.of ℤ)

set_option maxHeartbeats 1700000 in
private theorem openPiece_H_succ_subsingleton (p : P K) (n : ℕ) :
    Subsingleton (Sheaf.H (affineOpenDivisorPiece K R j p) (n + 1)) := by
  let G := fullPiece K p
  let D := affineOpenDivisorPiece K R j p
  let e₀ := SmallEtaleCohomologyComparison.sheafCohomologyEquiv R D (n + 1)
  let e₁ : (EV R).functor.obj D ≅ (restriction j).obj G :=
    (EV R).counitIso.app _ ≪≫ (restriction j).mapIso ((E K).counitIso.app G)
  let e₂ := ((Sheaf.functorH (V R).smallEtaleTopology (n + 1)).mapIso e₁).addCommGroupIsoToAddEquiv
  let e := e₀.trans e₂
  have h := OpenEtaleSkyscraperRestriction.restriction_H_succ_subsingleton
    j (x K p) (AddCommGrpCat.of ℤ) n
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

set_option maxHeartbeats 2200000 in
/-- The native restricted divisor sheaf has zero H¹ on every affine
open of the affine line. -/
theorem restrictedDivisor_HOne_subsingleton :
    Subsingleton (Sheaf.H ((restriction j).obj (divisorSheaf K)) 1) := by
  let D := (affineOpenRestriction K R j).obj (affineDivisorSheaf K)
  let h : Subsingleton (Sheaf.H (affineEtaleDirectSum (V R) (affineOpenDivisorPiece K R j)) 1) :=
    affineEtaleDirectSum_HOne_subsingleton (V R) (affineOpenDivisorPiece K R j)
      (KummerAffineCohomology.affineTerminal_isTerminal R) (fun t ↦
        finiteDirectSum_H_subsingleton (V R) (fun p : t ↦ affineOpenDivisorPiece K R j p.val) 1
          (fun p ↦ openPiece_H_succ_subsingleton K R j p.val 0))
  let eS := ((Sheaf.functorH (Scheme.AffineEtale.topology (V R)) 1).mapIso
    (affineRestrictedDivisorIso K R j)).addCommGroupIsoToAddEquiv
  let e₀ := SmallEtaleCohomologyComparison.sheafCohomologyEquiv R D 1
  let e₁ := ((Sheaf.functorH (V R).smallEtaleTopology 1).mapIso
    ((EV R).counitIso.app ((restriction j).obj (divisorSheaf K)))).addCommGroupIsoToAddEquiv
  let e := (e₀.trans e₁).symm.trans eS
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.restrictedDivisor_HOne_subsingleton
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
