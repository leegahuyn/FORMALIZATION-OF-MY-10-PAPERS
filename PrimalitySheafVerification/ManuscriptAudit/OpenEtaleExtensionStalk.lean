import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtension

/-!
# Étale stalk of an extension by zero outside the open

An étale neighborhood of a geometric point outside the open admits no
morphism to an object coming from the open. The pointwise left Kan
extension therefore has zero values on all such pointed neighborhoods.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem noKanArrow
    (hs : ¬ ∃ t : Spec (.of Ω) ⟶ U, t ≫ j = s)
    (W : X.Etale) (w : (Scheme.pointSmallEtale s).fiber.obj W)
    (a : CostructuredArrow (etalePostcompose j).op (op W)) : False := by
  let V : U.Etale := a.left.unop
  let f : W ⟶ (etalePostcompose j).obj V := a.hom.unop
  let t : Over.mk s ⟶ (Scheme.Etale.forget X).obj W := w
  have hf : f.left ≫ (V.hom ≫ j) = W.hom := by
    simpa only [MorphismProperty.Over.map_obj_hom] using MorphismProperty.Over.w f
  have ht : t.left ≫ W.hom = s := Over.w t
  exact hs ⟨t.left ≫ f.left ≫ V.hom, by simpa only [Category.assoc, hf] using ht⟩

/-- The actual extension by zero has zero stalk at a geometric point
that does not factor through the open. -/
theorem extensionByZero_stalk_isZero
    (hs : ¬ ∃ t : Spec (.of Ω) ⟶ U, t ≫ j = s)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj
      ((extensionByZero j AddCommGrpCat.{u}).obj F)) := by
  let C := AddCommGrpCat.{u}
  let Φ := Scheme.pointSmallEtale s
  let G := (etalePostcompose j).op
  letI := hasLeftKanExtension j C
  letI := hasPointwiseLeftKanExtension j C F.obj
  let P := G.lan.obj F.obj
  have hValue (W : X.Etale) (w : Φ.fiber.obj W) : IsZero (P.obj (op W)) := by
    apply (Iso.isZero_iff (G.leftKanExtensionObjIsoColimit F.obj (op W))).mpr
    apply (IsZero.iff_id_eq_zero _).mpr
    apply colimit.hom_ext
    intro a
    exact (noKanArrow j s hs W w a).elim
  have hStalk : IsZero ((Φ.presheafFiber (A := C)).obj P) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Φ.presheafFiber_hom_ext
    intro W w
    exact (hValue W w).eq_of_src _ _
  change IsZero ((Φ.sheafFiber (A := C)).obj ((presheafToSheaf X.smallEtaleTopology C).obj P))
  exact hStalk.of_iso ((Φ.presheafToSheafCompSheafFiberIso C).app P)

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleExtension.extensionByZero_stalk_isZero
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
