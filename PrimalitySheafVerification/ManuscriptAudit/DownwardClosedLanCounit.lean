import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-! Pointwise behavior of the presheaf restriction counit: identity
up to isomorphism on the open, zero source off the open. -/

namespace ManuscriptAudit.DownwardClosedLanCounit

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D A : Type*} [Category* C] [Category* D] [Category* A] [HasZeroObject A]
variable (L : C ⥤ D) [L.Full] [L.Faithful]
variable [∀ F : C ⥤ A, L.HasLeftKanExtension F]
variable (F : D ⥤ A) [L.HasPointwiseLeftKanExtension (L ⋙ F)]

abbrev counit := (L.lanAdjunction A).counit.app F

private theorem counit_at_obj_isIso (V : C) : IsIso ((counit L F).app (L.obj V)) := by
  let u := (L.lanUnit.app (L ⋙ F)).app V
  letI : IsIso u := inferInstanceAs (IsIso ((L.lanUnit.app (L ⋙ F)).app V))
  have h : u ≫ (counit L F).app (L.obj V) = 𝟙 _ :=
    L.lanUnit_app_app_lanAdjunction_counit_app_app F V
  have e : (counit L F).app (L.obj V) = inv u := by
    apply (cancel_epi u).mp
    rw [h, IsIso.hom_inv_id]
  rw [e]
  infer_instance

/-- The counit component over any chart in the essential image is an isomorphism. -/
theorem counit_at_iso_isIso {V : C} {W : D} (e : L.obj V ≅ W) : IsIso ((counit L F).app W) := by
  let G := L.lan.obj (L ⋙ F)
  let d : G ⟶ F := counit L F
  letI : IsIso (d.app (L.obj V)) := counit_at_obj_isIso L F V
  have hNat : G.map e.hom ≫ d.app W = d.app (L.obj V) ≫ F.map e.hom := d.naturality e.hom
  have h : d.app W = G.map e.inv ≫ d.app (L.obj V) ≫ F.map e.hom := by
    rw [← hNat, ← Category.assoc, ← Functor.map_comp,
      e.inv_hom_id, Functor.map_id, Category.id_comp]
  change IsIso (d.app W)
  rw [h]
  infer_instance

/-- At an object with empty Kan indexing category the source is the zero object. -/
def source_isZero (W : D) [IsEmpty (CostructuredArrow L W)] :
    IsZero ((L.lan.obj (L ⋙ F)).obj W) := by
  let H := L.isPointwiseLeftKanExtensionLeftKanExtensionUnit (L ⋙ F) W
  let E := Functor.LeftExtension.mk (L.leftKanExtension (L ⋙ F)) (L.leftKanExtensionUnit (L ⋙ F))
  let h : IsInitial ((L.lan.obj (L ⋙ F)).obj W) := (isColimitEquivIsInitialOfIsEmpty A (E.coconeAt W)) H
  exact (isZero_zero A).of_iso (h.uniqueUpToIso (isZero_zero A).isInitial)

/-- The presheaf counit is pointwise mono when any object receiving an arrow
from the image already lies in that essential image. -/
theorem counit_component_mono
    (hDown : ∀ W : D, CostructuredArrow L W → ∃ V : C, Nonempty (L.obj V ≅ W))
    (W : D) : Mono ((counit L F).app W) := by
  by_cases h : Nonempty (CostructuredArrow L W)
  · obtain ⟨a⟩ := h
    obtain ⟨V, ⟨e⟩⟩ := hDown W a
    letI := counit_at_iso_isIso L F e
    infer_instance
  · letI : IsEmpty (CostructuredArrow L W) := ⟨fun a ↦ h ⟨a⟩⟩
    exact (source_isZero L F W).mono _

end
end ManuscriptAudit.DownwardClosedLanCounit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DownwardClosedLanCounit.counit_at_iso_isIso,
      ``ManuscriptAudit.DownwardClosedLanCounit.counit_component_mono] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
