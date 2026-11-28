import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.MayerVietorisSectionConnecting

/-! A genuine overlap unit that lifts in the middle sheaf defines a
global quotient section and the expected actual Mayer–Vietoris class. -/

namespace ManuscriptAudit.MayerVietorisCokernelBoundaryLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleCohomologyPresheafZero EtalePresheafHOneRepresentatives
open MayerVietorisSectionConnecting

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {X : Scheme.{u}} (S : X.smallEtaleTopology.MayerVietorisSquare)
variable {F I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (i : F ⟶ I) [Mono i]
private abbrev Q := cokernel i
private abbrev p := cokernel.π i

/-- A local lift on the left piece with zero section on the right yields
one global quotient section with precisely the native boundary class. -/
theorem exists_cokernel_lift
    (a : I.obj.obj (op S.X₂)) (w : F.obj.obj (op S.X₁))
    (ha : I.obj.map S.f₁₂.op a = i.hom.app (op S.X₁) w) :
    ∃ z : (Q i).obj.obj (op S.X₄),
      (Q i).obj.map S.f₂₄.op z = (p i).hom.app (op S.X₂) a ∧
      (Q i).obj.map S.f₃₄.op z = 0 ∧
      connectingAt i S.X₄ z = S.δ F 0 1 rfl ((equivZero F S.X₁).symm w) := by
  let Q' := (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj (Q i)
  have h := S.sheafCondition_of_sheaf Q'
  have hCompat : (Q i).obj.map S.f₁₂.op ((p i).hom.app (op S.X₂) a) =
      (Q i).obj.map S.f₁₃.op 0 := by
    calc
      _ = (p i).hom.app (op S.X₁) (I.obj.map S.f₁₂.op a) :=
        (NatTrans.naturality_apply (p i).hom S.f₁₂.op a).symm
      _ = (p i).hom.app (op S.X₁) (i.hom.app (op S.X₁) w) := congrArg _ ha
      _ = 0 := congrArg (fun g : F ⟶ Q i => g.hom.app (op S.X₁) w) (cokernel.condition i)
      _ = _ := (map_zero ((Q i).obj.map S.f₁₃.op).hom).symm
  let z := h.glue ((p i).hom.app (op S.X₂) a) 0 hCompat
  have h₁ : (Q i).obj.map S.f₂₄.op z = (p i).hom.app (op S.X₂) a :=
    h.map_f₂₄_op_glue _ _ hCompat
  have h₂ : (Q i).obj.map S.f₃₄.op z = 0 := h.map_f₃₄_op_glue _ _ hCompat
  refine ⟨z, h₁, h₂, connectingAt_eq_mv S i z a 0 w h₁.symm ?_ ?_⟩
  · exact (map_zero ((p i).hom.app (op S.X₃)).hom).trans h₂.symm
  · rw [map_zero, sub_zero]
    exact ha

end

end ManuscriptAudit.MayerVietorisCokernelBoundaryLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MayerVietorisCokernelBoundaryLift.exists_cokernel_lift
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
