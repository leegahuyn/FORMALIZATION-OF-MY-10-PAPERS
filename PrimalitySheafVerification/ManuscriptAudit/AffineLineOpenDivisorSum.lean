import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorSheaf
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleCoproduct

/-! The restriction of the actual affine-line divisor coproduct to an affine open. -/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleObjectRestriction FiniteSupportPresheaf IsDedekindDomain

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

private abbrev affinePiece (p : P K) := (E K).inverse.obj (fullPiece K p)

/-- Restriction from the affine line to its affine open, on affine-sheaf sites. -/
abbrev affineOpenRestriction := (E K).functor ⋙ restriction j ⋙ (EV R).inverse

/-- The open restriction of one geometric summand of the divisor sheaf. -/
abbrev affineOpenDivisorPiece (p : P K) := (affineOpenRestriction K R j).obj (affinePiece K p)

/-- Restriction carries the actual divisor coproduct to the coproduct
of the open restrictions of its geometric summands. -/
set_option maxHeartbeats 2600000 in
def affineRestrictedDivisorIso :
    (affineOpenRestriction K R j).obj (affineDivisorSheaf K) ≅
      affineEtaleDirectSum (V R) (affineOpenDivisorPiece K R j) := by
  let Q := affineOpenRestriction K R j
  let a := (E K).toAdjunction.comp ((restrictionAdjunction j).comp (EV R).symm.toAdjunction)
  letI : PreservesColimitsOfSize.{0, 0} Q := a.leftAdjoint_preservesColimits
  let F₀ := affinePiece K
  let c : Cofan F₀ := Cofan.mk (affineDivisorSheaf K) (summand (X K) F₀)
  let h : IsColimit c := affineEtaleDirectSumIsColimit (X K) F₀
  let hMapped : IsColimit (Q.mapCocone c) := isColimitOfPreserves Q h
  let h' := (Cofan.isColimitMapCoconeEquiv Q F₀ c) hMapped
  exact h'.coconePointUniqueUpToIso
    (affineEtaleDirectSumIsColimit (V R) (affineOpenDivisorPiece K R j))

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.affineRestrictedDivisorIso
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
