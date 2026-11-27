import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.InjectiveCechPullback
import PrimalitySheafVerification.ManuscriptAudit.SheafHOnePushout
import PrimalitySheafVerification.ManuscriptAudit.SingletonCoverRefinement

/-! A local coboundary kills the native degree-one cokernel class. -/

namespace ManuscriptAudit.SheafCechCokernel

open CategoryTheory CategoryTheory.Limits Opposite
open InjectiveCechPullback SingletonCoverRefinement

universe u v w w'

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable {Q M : Sheaf J AddCommGrpCat.{w}} (j : Q ⟶ M) [Mono j]
variable {U T : C} (f : U ⟶ T)

/-- If the image of the difference cocycle becomes a coboundary,
the corresponding image of the native H¹ class is zero. -/
theorem map_connecting_eq_zero_of_coboundary {Q' : Sheaf J AddCommGrpCat.{w}} (u : Q ⟶ Q')
    (hT : IsTerminal T) (hf : Covers J f)
    (x : (cokernel j).obj.obj (op T)) (y : M.obj.obj (op U))
    (hy : (cokernel.π j).hom.app (op U) y = (cokernel j).obj.map f.op x)
    (b : Q.obj.obj (op (Double f)))
    (hb : j.hom.app (op (Double f)) b = M.obj.map (second f).op y - M.obj.map (first f).op y)
    (a : Q'.obj.obj (op U))
    (ha : u.hom.app (op (Double f)) b = Q'.obj.map (second f).op a -
      Q'.obj.map (first f).op a) :
    Sheaf.H.map u 1 (SheafH1Descent.connectingSection j hT x) = 0 := by
  let W := Double f
  let N := pushout j u
  let e : M ⟶ N := pushout.inl j u
  let k : Q' ⟶ N := pushout.inr j u
  let p : N ⟶ cokernel j := (CokernelPushout.sequence j u).g
  let y' := e.hom.app (op U) y
  let z := y' - k.hom.app (op U) a
  have hDiff : N.obj.map (second f).op y' - N.obj.map (first f).op y' =
      k.hom.app (op W) (u.hom.app (op W) b) := by
    change N.obj.map (second f).op (e.hom.app (op U) y) -
      N.obj.map (first f).op (e.hom.app (op U) y) = _
    rw [← NatTrans.naturality_apply e.hom (second f).op y,
      ← NatTrans.naturality_apply e.hom (first f).op y]
    change (e.hom.app (op W)).hom _ - (e.hom.app (op W)).hom _ = _
    rw [← map_sub]
    change e.hom.app (op W) (M.obj.map (second f).op y - M.obj.map (first f).op y) = _
    rw [← hb]
    exact ConcreteCategory.congr_hom
      (congrArg (fun m : Q ⟶ N ↦ m.hom.app (op W))
        (pushout.condition (f := j) (g := u))) b
  have hzPair : N.obj.map (first f).op z = N.obj.map (second f).op z := by
    have hL : N.obj.map (first f).op (k.hom.app (op U) a) =
        k.hom.app (op W) (Q'.obj.map (first f).op a) :=
      (NatTrans.naturality_apply k.hom (first f).op a).symm
    have hR : N.obj.map (second f).op (k.hom.app (op U) a) =
        k.hom.app (op W) (Q'.obj.map (second f).op a) :=
      (NatTrans.naturality_apply k.hom (second f).op a).symm
    have hk : N.obj.map (second f).op (k.hom.app (op U) a) -
        N.obj.map (first f).op (k.hom.app (op U) a) =
        N.obj.map (second f).op y' - N.obj.map (first f).op y' := by
      rw [hL, hR]
      change (k.hom.app (op W)).hom _ - (k.hom.app (op W)).hom _ = _
      rw [← map_sub]
      exact (congrArg (fun x ↦ k.hom.app (op W) x) ha.symm).trans hDiff.symm
    apply Eq.symm
    apply sub_eq_zero.mp
    change (N.obj.map (second f).op).hom (y' - k.hom.app (op U) a) -
      (N.obj.map (first f).op).hom (y' - k.hom.app (op U) a) = 0
    rw [map_sub, map_sub]
    calc
      _ = (N.obj.map (second f).op y' - N.obj.map (first f).op y') -
        (N.obj.map (second f).op (k.hom.app (op U) a) -
          N.obj.map (first f).op (k.hom.app (op U) a)) := by abel
      _ = 0 := by rw [hk, sub_self]
  have hzImage : p.hom.app (op U) z = (cokernel j).obj.map f.op x := by
    have he : p.hom.app (op U) y' = (cokernel.π j).hom.app (op U) y :=
      ConcreteCategory.congr_hom
        (congrArg (fun m : M ⟶ cokernel j ↦ m.hom.app (op U))
          (CokernelPushout.inl_sequence_g j u)) y
    have hk : p.hom.app (op U) (k.hom.app (op U) a) = 0 :=
      ConcreteCategory.congr_hom
        (congrArg (fun m : Q' ⟶ cokernel j ↦ m.hom.app (op U))
          (CokernelPushout.sequence j u).zero) a
    change (p.hom.app (op U)).hom (y' - k.hom.app (op U) a) = _
    rw [map_sub]
    change p.hom.app (op U) y' - p.hom.app (op U) (k.hom.app (op U) a) = _
    rw [he, hk, sub_zero, hy]
  obtain ⟨z₀, hz₀⟩ := exists_amalgamation J N f hf z hzPair
  have hz₀Image : p.hom.app (op T) z₀ = x := by
    apply restriction_injective J (cokernel j) f hf
    rw [← NatTrans.naturality_apply p.hom f.op z₀, hz₀]
    exact hzImage
  exact SheafHOnePushout.map_connecting_eq_zero_of_lift j u hT x z₀ hz₀Image

end

end ManuscriptAudit.SheafCechCokernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.SheafCechCokernel.map_connecting_eq_zero_of_coboundary
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
