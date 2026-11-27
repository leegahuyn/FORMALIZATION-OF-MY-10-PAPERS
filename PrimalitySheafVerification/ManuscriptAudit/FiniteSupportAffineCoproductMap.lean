import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Limits
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleCoproduct

/-! Left adjoints preserve the actual finite-support sheaf coproduct. -/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1100000

private abbrev Aff (S : Scheme.{0}) :=
  Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0}

variable {S T : Scheme.{0}} {I : Type}

/-- A left adjoint carries a finite-support affine étale sheaf
coproduct to the finite-support coproduct of the images. -/
def mapAffineDirectSumIso (F : Aff S ⥤ Aff T) {G : Aff T ⥤ Aff S}
    (a : F ⊣ G) (P : I → Aff S) :
    F.obj (affineEtaleDirectSum S P) ≅ affineEtaleDirectSum T (fun i ↦ F.obj (P i)) := by
  letI : PreservesColimitsOfSize.{0, 0} F := a.leftAdjoint_preservesColimits
  let c : Cofan P := Cofan.mk (affineEtaleDirectSum S P) (summand S P)
  have h : IsColimit c := affineEtaleDirectSumIsColimit S P
  let hMap : IsColimit (F.mapCocone c) := isColimitOfPreserves F h
  let hCofan := (Cofan.isColimitMapCoconeEquiv F P c) hMap
  exact hCofan.coconePointUniqueUpToIso
    (affineEtaleDirectSumIsColimit T (fun i ↦ F.obj (P i)))

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.FiniteSupportPresheaf.mapAffineDirectSumIso
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
