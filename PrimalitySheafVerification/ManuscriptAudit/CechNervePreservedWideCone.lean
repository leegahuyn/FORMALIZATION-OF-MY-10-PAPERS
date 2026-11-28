import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Connected
import PrimalitySheafVerification.ManuscriptAudit.CechNerveLowDegrees

/-! The actual site nerve, sent to schemes, remains the corresponding
wide pullback and retains its canonical legs. -/

namespace ManuscriptAudit.CechNervePreservedWideCone

open CategoryTheory CategoryTheory.Limits
open CechNerveLowDegrees (N vertex)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [HasFiniteLimits C]
  (F : C ⥤ D) {U T : C} (f : U ⟶ T) (n : ℕ)

private abbrev I := Fin (n + 1)
private abbrev P := WidePullbackShape.wideCospan T (fun _ : I (n := n) ↦ U) fun _ ↦ f
private abbrev Q := WidePullbackShape.wideCospan (F.obj T) (fun _ : I (n := n) ↦ F.obj U)
  fun _ ↦ F.map f

private def diagramIso : P f n ⋙ F ≅ Q F f n :=
  WidePullbackShape.diagramIsoWideCospan (P f n ⋙ F)

private abbrev sourceCone := F.mapCone (limit.cone (P f n))

/-- The mapped actual nerve cone. -/
def cone : WidePullbackCone (fun _ : I (n := n) ↦ F.map f) :=
  (Cone.postcompose (diagramIso F f n).hom).obj (sourceCone F f n)

/-- The preserved actual wide pullback is a limit in the receiving category. -/
def isLimit_cone [PreservesLimit (P f n) F] : IsLimit (cone F f n) :=
  (IsLimit.postcomposeHomEquiv (diagramIso F f n) (sourceCone F f n)).symm
    (isLimitOfPreserves F (limit.isLimit (P f n)))

/-- The vertices are literally the images of the original vertices. -/
theorem cone_π (i : I (n := n)) : (cone F f n).π i = F.map (vertex f n i) := by
  change F.map (vertex f n i) ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem cone_base :
    (cone F f n).base = F.map (WidePullback.base (fun _ : I (n := n) ↦ f)) := by
  change F.map (WidePullback.base (fun _ : I (n := n) ↦ f)) ≫ 𝟙 _ = _
  exact Category.comp_id _

end
end ManuscriptAudit.CechNervePreservedWideCone

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CechNervePreservedWideCone.isLimit_cone
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
