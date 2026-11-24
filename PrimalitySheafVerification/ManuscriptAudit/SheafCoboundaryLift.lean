import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-!
# Correcting a local sheaf lift by an overlap coboundary

If the difference of two restrictions of a lift on the actual double
overlap is the coboundary of a section on the cover, subtracting that
section makes the lift compatible. The sheaf axiom then gives a global
lift of the prescribed cokernel section.
-/

namespace ManuscriptAudit.SheafCoboundaryLift

open CategoryTheory CategoryTheory.Limits Opposite
open SheafSectionDifference

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I)

/-- The two restrictions of a local lift have equal image on its double overlap. -/
theorem same_image_on_overlap {T U D : C} (f : U ⟶ T) (r₁ r₂ : D ⟶ U)
    (hw : r₁ ≫ f = r₂ ≫ f)
    (x : (cokernel i).obj.obj (op T)) (y : I.obj.obj (op U))
    (hy : (cokernel.π i).hom.app (op U) y = (cokernel i).obj.map f.op x) :
    (cokernel.π i).hom.app (op D) (I.obj.map r₁.op y) =
      (cokernel.π i).hom.app (op D) (I.obj.map r₂.op y) := by
  have h (r : D ⟶ U) :
      (cokernel.π i).hom.app (op D) (I.obj.map r.op y) =
        (cokernel i).obj.map (r ≫ f).op x := by
    rw [NatTrans.naturality_apply, hy, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rw [h r₁, h r₂, hw]

variable [Mono i] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- A coboundary on the actual double overlap removes the obstruction to gluing. -/
theorem exists_global_lift_of_double_overlap_coboundary {T U D : C}
    (f : U ⟶ T) (r₁ r₂ : D ⟶ U) (hP : IsPullback r₁ r₂ f f)
    (hCover : Sieve.generate (Presieve.singleton f) ∈ J T)
    (x : (cokernel i).obj.obj (op T)) (y : I.obj.obj (op U))
    (hy : (cokernel.π i).hom.app (op U) y = (cokernel i).obj.map f.op x)
    (b : F.obj.obj (op U))
    (hb : difference i D (I.obj.map r₁.op y) (I.obj.map r₂.op y)
        (same_image_on_overlap i f r₁ r₂ hP.w x y hy) =
        F.obj.map r₁.op b - F.obj.map r₂.op b) :
    ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  let q := cokernel.π i
  let z := y - i.hom.app (op U) b
  have hzq : q.hom.app (op U) z = (cokernel i).obj.map f.op x := by
    have hzero := (cokernel_sections_exact i U (i.hom.app (op U) b)).2 ⟨b, rfl⟩
    change (q.hom.app (op U)).hom (y - i.hom.app (op U) b) = _
    rw [map_sub]
    change q.hom.app (op U) y - q.hom.app (op U) (i.hom.app (op U) b) = _
    rw [hy, hzero, sub_zero]
  have hD := difference_spec i D (I.obj.map r₁.op y) (I.obj.map r₂.op y)
    (same_image_on_overlap i f r₁ r₂ hP.w x y hy)
  rw [hb] at hD
  change (i.hom.app (op D)).hom (F.obj.map r₁.op b - F.obj.map r₂.op b) = _ at hD
  rw [map_sub] at hD
  change i.hom.app (op D) (F.obj.map r₁.op b) - i.hom.app (op D) (F.obj.map r₂.op b) =
    I.obj.map r₁.op y - I.obj.map r₂.op y at hD
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply] at hD
  have hzD : I.obj.map r₁.op z = I.obj.map r₂.op z := by
    change (I.obj.map r₁.op).hom (y - i.hom.app (op U) b) =
      (I.obj.map r₂.op).hom (y - i.hom.app (op U) b)
    rw [map_sub, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hD.symm
  apply SheafH1Descent.exists_global_lift_of_compatible_cover f hCover q x z hzq
  intro W g h hw
  let t := hP.lift g h hw
  have hg : t ≫ r₁ = g := hP.lift_fst g h hw
  have hh : t ≫ r₂ = h := hP.lift_snd g h hw
  calc
    I.obj.map g.op z = I.obj.map t.op (I.obj.map r₁.op z) := by
      rw [← hg, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    _ = I.obj.map t.op (I.obj.map r₂.op z) := congrArg (fun a => I.obj.map t.op a) hzD
    _ = I.obj.map h.op z := by
      rw [← hh, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

end ManuscriptAudit.SheafCoboundaryLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafCoboundaryLift.same_image_on_overlap,
      ``ManuscriptAudit.SheafCoboundaryLift.exists_global_lift_of_double_overlap_coboundary] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
