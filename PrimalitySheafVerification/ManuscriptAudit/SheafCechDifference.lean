import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.InjectiveCechPullback
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-! Čech differences of native local cokernel lifts. -/

namespace ManuscriptAudit.SheafCechCokernel

open CategoryTheory CategoryTheory.Limits Opposite
open InjectiveCechPullback

universe u v w

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
variable {Q M : Sheaf J AddCommGrpCat.{w}} (j : Q ⟶ M) [Mono j]
variable {U T : C} (f : U ⟶ T)

private theorem restrict_restrict (A : Sheaf J AddCommGrpCat.{w}) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : A.obj.obj (op Z)) :
    A.obj.map a.op (A.obj.map b.op x) = A.obj.map (a ≫ b).op x := by
  rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]

/-- The difference of the two pullbacks of a local lift is a native
Čech cocycle of the kernel sheaf. -/
theorem exists_cocycle_of_local_lift (x : (cokernel j).obj.obj (op T)) (y : M.obj.obj (op U))
    (hy : (cokernel.π j).hom.app (op U) y = (cokernel j).obj.map f.op x) :
    ∃ b : Q.obj.obj (op (Double f)),
      j.hom.app (op (Double f)) b = M.obj.map (second f).op y - M.obj.map (first f).op y ∧
      Q.obj.map (edge23 f).op b - Q.obj.map (edge13 f).op b + Q.obj.map (edge12 f).op b = 0 := by
  let W := Double f
  let π := cokernel.π j
  have he : π.hom.app (op W) (M.obj.map (second f).op y) =
      π.hom.app (op W) (M.obj.map (first f).op y) := by
    rw [NatTrans.naturality_apply π.hom (second f).op y,
      NatTrans.naturality_apply π.hom (first f).op y, hy,
      restrict_restrict, restrict_restrict, pullback.condition (f := f) (g := f)]
  let b := SheafSectionDifference.difference j W
    (M.obj.map (second f).op y) (M.obj.map (first f).op y) he
  have hb : j.hom.app (op W) b = M.obj.map (second f).op y - M.obj.map (first f).op y :=
    SheafSectionDifference.difference_spec j W _ _ he
  refine ⟨b, hb, ?_⟩
  apply SheafSectionDifference.section_injective j (Triple f)
  have h (d : Triple f ⟶ W) :
      j.hom.app (op (Triple f)) (Q.obj.map d.op b) =
        M.obj.map (d ≫ second f).op y - M.obj.map (d ≫ first f).op y := by
    rw [NatTrans.naturality_apply j.hom d.op b, hb]
    change (M.obj.map d.op).hom (M.obj.map (second f).op y - M.obj.map (first f).op y) = _
    rw [map_sub]
    exact congrArg₂ (fun a b : M.obj.obj (op (Triple f)) ↦ a - b)
      (restrict_restrict M d (second f) y) (restrict_restrict M d (first f) y)
  have h23s : edge23 f ≫ second f = edge13 f ≫ second f := by
    rw [edge23, pullback.lift_snd]
  have h23f : edge23 f ≫ first f = edge12 f ≫ second f := by
    rw [edge23, pullback.lift_fst]
  have h13f : edge13 f ≫ first f = edge12 f ≫ first f :=
    (pullback.condition (f := first f) (g := first f)).symm
  change (j.hom.app (op (Triple f))).hom
    (Q.obj.map (edge23 f).op b - Q.obj.map (edge13 f).op b + Q.obj.map (edge12 f).op b) =
      (j.hom.app (op (Triple f))).hom 0
  rw [map_add, map_sub, map_zero]
  change j.hom.app _ (Q.obj.map (edge23 f).op b) - j.hom.app _ (Q.obj.map (edge13 f).op b) +
    j.hom.app _ (Q.obj.map (edge12 f).op b) = 0
  rw [h (edge23 f), h (edge13 f), h (edge12 f), h23s, h23f, h13f]
  abel

end

end ManuscriptAudit.SheafCechCokernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.SheafCechCokernel.exists_cocycle_of_local_lift
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
