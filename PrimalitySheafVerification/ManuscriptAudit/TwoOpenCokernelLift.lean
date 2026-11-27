import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-!
# Gluing local lifts across a two-object cover

Given a two-object cover by monomorphisms, the difference of the local
lifts on the pullback is a section of the kernel sheaf. If that section
can be lifted to one covering piece, correcting that piece makes the
local lifts glue to a global lift of the original section.
-/

namespace ManuscriptAudit.TwoOpenCokernelLift

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Objects of a family with two covering pieces. -/
def coverObjects (U V : C) : Bool → C
  | false => U
  | true => V

/-- Arrows of a family with two covering pieces. -/
def coverArrows {T U V : C} (u : U ⟶ T) (v : V ⟶ T) :
    (b : Bool) → coverObjects U V b ⟶ T
  | false => u
  | true => v

private abbrev A := AddCommGrpCat.{w}

private theorem restrict_restrict (P : Cᵒᵖ ⥤ A.{w}) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : P.obj (op Z)) :
    P.map f.op (P.map g.op a) = P.map (f ≫ g).op a := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

variable [HasSheafify J A.{w}] [J.HasSheafCompose (forget A.{w})]
variable {F I : Sheaf J A.{w}} (i : F ⟶ I) [Mono i]

/-- Local lifts glue if a given overlap difference extends to the first piece. -/
theorem exists_global_lift_of_difference {T U V D : C}
    (u : U ⟶ T) (v : V ⟶ T) [Mono u] [Mono v]
    (p : D ⟶ U) (q : D ⟶ V) (hD : IsPullback p q u v)
    (hCover : Sieve.ofArrows (coverObjects U V) (coverArrows u v) ∈ J T)
    (x : (cokernel i).obj.obj (op T))
    (a : I.obj.obj (op U)) (b : I.obj.obj (op V))
    (ha : (cokernel.π i).hom.app (op U) a = (cokernel i).obj.map u.op x)
    (hb : (cokernel.π i).hom.app (op V) b = (cokernel i).obj.map v.op x)
    (d : F.obj.obj (op D))
    (hd : i.hom.app (op D) d = I.obj.map p.op a - I.obj.map q.op b)
    (c : F.obj.obj (op U)) (hc : F.obj.map p.op c = d) :
    ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  let Q := cokernel i
  let π : I ⟶ Q := cokernel.π i
  let a' := a - i.hom.app (op U) c
  have hZero : π.hom.app (op U) (i.hom.app (op U) c) = 0 :=
    ConcreteCategory.congr_hom
      (congrArg (fun f : F ⟶ Q => f.hom.app (op U)) (cokernel.condition i)) c
  have ha' : π.hom.app (op U) a' = Q.obj.map u.op x := by
    change (π.hom.app (op U)).hom (a - i.hom.app (op U) c) = _
    rw [map_sub]
    change π.hom.app (op U) a - π.hom.app (op U) (i.hom.app (op U) c) = _
    rw [ha, hZero, sub_zero]
  have hOverlap : I.obj.map p.op a' = I.obj.map q.op b := by
    change (I.obj.map p.op).hom (a - i.hom.app (op U) c) = _
    rw [map_sub]
    change I.obj.map p.op a - I.obj.map p.op (i.hom.app (op U) c) = _
    rw [← NatTrans.naturality_apply i.hom p.op c, hc, hd, sub_sub_cancel]
  have hCross {W : C} (f : W ⟶ U) (g : W ⟶ V) (h : f ≫ u = g ≫ v) :
      I.obj.map f.op a' = I.obj.map g.op b := by
    let l := hD.lift f g h
    calc
      _ = I.obj.map l.op (I.obj.map p.op a') := by
        rw [restrict_restrict, hD.lift_fst f g h]
      _ = I.obj.map l.op (I.obj.map q.op b) := by rw [hOverlap]
      _ = _ := by rw [restrict_restrict, hD.lift_snd f g h]
  let forgetA := forget A.{w}
  let P := I.obj ⋙ forgetA
  let y (d : Bool) : P.obj (op (coverObjects U V d)) :=
    match d with
    | false => a'
    | true => b
  have hCompat : Presieve.Arrows.Compatible P (coverArrows u v) y := by
    intro first second W f g h
    cases first <;> cases second
    · change f ≫ u = g ≫ u at h
      cases (cancel_mono u).mp h
      rfl
    · exact hCross f g h
    · exact (hCross g f h.symm).symm
    · change f ≫ v = g ≫ v at h
      cases (cancel_mono v).mp h
      rfl
  have hI : Presieve.IsSheaf J P :=
    (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J forgetA).obj I).property
  have hQ : Presieve.IsSheaf J (Q.obj ⋙ forgetA) :=
    (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J forgetA).obj Q).property
  let R := Presieve.ofArrows (coverObjects U V) (coverArrows u v)
  have hRCover : Sieve.generate R ∈ J T := hCover
  obtain ⟨z, hz, _⟩ := (Presieve.isSheafFor_arrows_iff (P := P) (π := coverArrows u v)).mp
    (hI.isSheafFor R hRCover) y hCompat
  have hzU : I.obj.map u.op z = a' := hz false
  have hzV : I.obj.map v.op z = b := hz true
  refine ⟨z, (hQ.isSheafFor R hRCover).isSeparatedFor.ext ?_⟩
  rintro _ _ ⟨side⟩
  cases side
  · change Q.obj.map u.op (π.hom.app (op T) z) = Q.obj.map u.op x
    rw [← NatTrans.naturality_apply π.hom u.op z, hzU]
    exact ha'
  · change Q.obj.map v.op (π.hom.app (op T) z) = Q.obj.map v.op x
    rw [← NatTrans.naturality_apply π.hom v.op z, hzV]
    exact hb

/-- Local lifts on two monomorphic covering pieces glue after a kernel correction
from the first piece, provided its restriction to the pullback is surjective. -/
theorem exists_global_lift {T U V D : C}
    (u : U ⟶ T) (v : V ⟶ T) [Mono u] [Mono v]
    (p : D ⟶ U) (q : D ⟶ V) (hD : IsPullback p q u v)
    (hCover : Sieve.ofArrows (coverObjects U V) (coverArrows u v) ∈ J T)
    (hRestrict : Function.Surjective (F.obj.map p.op))
    (x : (cokernel i).obj.obj (op T))
    (a : I.obj.obj (op U)) (b : I.obj.obj (op V))
    (ha : (cokernel.π i).hom.app (op U) a = (cokernel i).obj.map u.op x)
    (hb : (cokernel.π i).hom.app (op V) b = (cokernel i).obj.map v.op x) :
    ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  let Q := cokernel i
  let π : I ⟶ Q := cokernel.π i
  have hπ : π.hom.app (op D) (I.obj.map p.op a) = π.hom.app (op D) (I.obj.map q.op b) := by
    rw [NatTrans.naturality_apply π.hom p.op a, NatTrans.naturality_apply π.hom q.op b, ha, hb]
    change Q.obj.map p.op (Q.obj.map u.op x) = Q.obj.map q.op (Q.obj.map v.op x)
    rw [restrict_restrict Q.obj p u x, restrict_restrict Q.obj q v x, hD.w]
  obtain ⟨d, hd, _⟩ := SheafSectionDifference.existsUnique_difference i D
    (I.obj.map p.op a) (I.obj.map q.op b) hπ
  obtain ⟨c, hc⟩ := hRestrict d
  exact exists_global_lift_of_difference i u v p q hD hCover x a b ha hb d hd c hc

end

end ManuscriptAudit.TwoOpenCokernelLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.TwoOpenCokernelLift.exists_global_lift_of_difference,
      ``ManuscriptAudit.TwoOpenCokernelLift.exists_global_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName ↦ !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
