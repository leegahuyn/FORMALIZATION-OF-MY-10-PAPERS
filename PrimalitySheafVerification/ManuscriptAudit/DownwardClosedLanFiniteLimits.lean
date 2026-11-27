import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-! A pointwise left Kan extension along a fully faithful functor
with downward-closed image preserves finite limits in an abelian target. -/

namespace ManuscriptAudit.DownwardClosedLanFiniteLimits

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  [HasZeroObject A] [HasFiniteLimits A]
variable (L : C ⥤ D) [L.Full] [L.Faithful]
variable [∀ F : C ⥤ A, L.HasLeftKanExtension F]
variable (hPoint : ∀ F : C ⥤ A, L.HasPointwiseLeftKanExtension F)

/-- Over an object in the essential image, evaluation of the Kan extension
is evaluation of the input at the original object. -/
private def evaluationIso {V : C} {W : D} (e : L.obj V ≅ W) :
    (evaluation C A).obj V ≅ L.lan ⋙ (evaluation D A).obj W := by
  let i : (evaluation C A).obj V ≅ L.lan ⋙ (evaluation D A).obj (L.obj V) :=
    NatIso.ofComponents (fun F ↦ by
      letI := hPoint F
      exact asIso ((L.lanUnit.app F).app V)) (by
        intro F G f
        exact congrArg (fun η ↦ η.app V) (L.lanUnit.naturality f))
  let j : L.lan ⋙ (evaluation D A).obj (L.obj V) ≅ L.lan ⋙ (evaluation D A).obj W :=
    NatIso.ofComponents (fun F ↦ (L.lan.obj F).mapIso e) (fun f ↦
      ((L.lan.map f).naturality e.hom).symm)
  exact i ≪≫ j

/-- At any object admitting no arrows from the image, the left Kan
extension is the zero object, independently of the input. -/
private def isZeroAt (W : D) [IsEmpty (CostructuredArrow L W)] (F : C ⥤ A) :
    IsZero ((L.lan.obj F).obj W) := by
  letI := hPoint F
  let H := L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F W
  let h := (isColimitEquivIsInitialOfIsEmpty _).mp H
  exact (isZero_zero A).of_iso (h.uniqueUpToIso zeroIsInitial)

include hPoint in
/-- If every object receiving an arrow from the image is in the
essential image, the pointwise left Kan extension preserves finite limits. -/
theorem lan_preservesFiniteLimits
    (hDown : ∀ W : D, CostructuredArrow L W → ∃ V : C, Nonempty (L.obj V ≅ W)) :
    PreservesFiniteLimits (L.lan : (C ⥤ A) ⥤ D ⥤ A) := by
  apply preservesFiniteLimits_of_evaluation
  intro W
  by_cases hb : Nonempty (CostructuredArrow L W)
  · obtain ⟨a⟩ := hb
    obtain ⟨V, ⟨e⟩⟩ := hDown W a
    exact preservesFiniteLimits_of_natIso (evaluationIso L hPoint e)
  · letI : IsEmpty (CostructuredArrow L W) := ⟨fun a ↦ hb ⟨a⟩⟩
    refine ⟨fun I _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} _ ↦ ⟨?_⟩⟩⟩⟩
    refine
      { lift := fun s ↦ (isZeroAt L hPoint W c.pt).isTerminal.from s.pt
        fac := fun s i ↦ (isZeroAt L hPoint W (K.obj i)).isTerminal.hom_ext _ _
        uniq := fun s f _ ↦ (isZeroAt L hPoint W c.pt).isTerminal.hom_ext _ _ }

end
end ManuscriptAudit.DownwardClosedLanFiniteLimits

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DownwardClosedLanFiniteLimits.lan_preservesFiniteLimits
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
