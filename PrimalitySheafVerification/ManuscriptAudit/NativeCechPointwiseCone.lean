import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CechNerveLowDegrees

/-! The actual Čech nerve is objectwise contractible on each
nonempty fibre of maps to its base. The anchor is chosen separately
for each base arrow, so the construction applies to every cover. -/

namespace ManuscriptAudit.NativeCechPointwiseCone

open CategoryTheory CategoryTheory.Limits Opposite
open CechNerveLowDegrees (N vertex face face_vertex)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [HasFiniteLimits C]
  {U T W : C} (f : U ⟶ T)

private abbrev base (n : ℕ) : N f n ⟶ T :=
  WidePullback.base (fun _ : Fin (n + 1) ↦ f)

private theorem face_base (n : ℕ) (i : Fin (n + 2)) :
    face f n i ≫ base f n = base f (n + 1) := by
  change (Arrow.mk f).cechNerve.map (SimplexCategory.δ i).op ≫ base f n = _
  rw [Arrow.cechNerve_map]
  exact WidePullback.lift_base _ _ _ _

private def chooseLift (b : W ⟶ T) (h : ∃ a : W ⟶ U, a ≫ f = b) : W ⟶ U :=
  Classical.choose h

private theorem chooseLift_spec (b : W ⟶ T) (h : ∃ a : W ⟶ U, a ≫ f = b) :
    chooseLift f b h ≫ f = b :=
  Classical.choose_spec h

private def anchor (n : ℕ) (a : W ⟶ N f n) : W ⟶ U :=
  chooseLift f (a ≫ base f n) ⟨a ≫ vertex f n 0, by
    rw [Category.assoc]
    exact congrArg (fun m ↦ a ≫ m) (WidePullback.π_arrow (fun _ : Fin (n + 1) ↦ f) 0)⟩

private theorem anchor_spec (n : ℕ) (a : W ⟶ N f n) :
    anchor f n a ≫ f = a ≫ base f n :=
  chooseLift_spec f _ _

private theorem anchor_face (n : ℕ) (i : Fin (n + 2)) (a : W ⟶ N f (n + 1)) :
    anchor f n (a ≫ face f n i) = anchor f (n + 1) a := by
  unfold anchor
  simp only [Category.assoc, face_base]

/-- The prepend operation gives the actual map into the next Čech term. -/
def prepend (n : ℕ) (a : W ⟶ N f n) : W ⟶ N f (n + 1) :=
  WidePullback.lift (a ≫ base f n)
    (Fin.cases (anchor f n a) (fun i ↦ a ≫ vertex f n i)) (fun i ↦ by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact anchor_spec f n a
      · change (a ≫ vertex f n j) ≫ f = a ≫ base f n
        rw [Category.assoc]
        exact congrArg (fun m ↦ a ≫ m)
          (WidePullback.π_arrow (fun _ : Fin (n + 1) ↦ f) j))

private theorem prepend_base (n : ℕ) (a : W ⟶ N f n) :
    prepend f n a ≫ base f (n + 1) = a ≫ base f n :=
  WidePullback.lift_base _ _ _ _

private theorem prepend_vertex_zero (n : ℕ) (a : W ⟶ N f n) :
    prepend f n a ≫ vertex f (n + 1) 0 = anchor f n a :=
  WidePullback.lift_π (fun _ : Fin (n + 2) ↦ f) _ _ _ 0

private theorem prepend_vertex_succ (n : ℕ) (a : W ⟶ N f n) (i : Fin (n + 1)) :
    prepend f n a ≫ vertex f (n + 1) i.succ = a ≫ vertex f n i :=
  WidePullback.lift_π (fun _ : Fin (n + 2) ↦ f) _ _ _ i.succ

/-- Removing the preparatory vertex gives the original arrow. -/
theorem prepend_face_zero (n : ℕ) (a : W ⟶ N f n) :
    prepend f n a ≫ face f n 0 = a := by
  apply WidePullback.hom_ext
  · intro i
    rw [Category.assoc, face_vertex]
    change prepend f n a ≫ vertex f (n + 1) i.succ = a ≫ vertex f n i
    exact prepend_vertex_succ f n a i
  · rw [Category.assoc, face_base, prepend_base]

set_option maxHeartbeats 2600000 in
/-- Removing any later vertex commutes with prepending the anchor
of the same actual fibre. -/
theorem prepend_face_succ (n : ℕ) (i : Fin (n + 2)) (a : W ⟶ N f (n + 1)) :
    prepend f (n + 1) a ≫ face f (n + 1) i.succ =
      prepend f n (a ≫ face f n i) := by
  apply WidePullback.hom_ext
  · intro k
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · rw [Category.assoc, face_vertex]
      change prepend f (n + 1) a ≫ vertex f (n + 2) (i.succ.succAbove 0) =
        prepend f n (a ≫ face f n i) ≫ vertex f (n + 1) 0
      rw [Fin.succ_succAbove_zero, prepend_vertex_zero, prepend_vertex_zero, anchor_face]
    · rw [Category.assoc, face_vertex]
      change prepend f (n + 1) a ≫ vertex f (n + 2) (i.succ.succAbove j.succ) =
        prepend f n (a ≫ face f n i) ≫ vertex f (n + 1) j.succ
      rw [Fin.succ_succAbove_succ, prepend_vertex_succ, prepend_vertex_succ,
        Category.assoc, face_vertex] <;> rfl
  · rw [Category.assoc, face_base, prepend_base, prepend_base, Category.assoc, face_base]

end
end ManuscriptAudit.NativeCechPointwiseCone

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeCechPointwiseCone.prepend_face_zero,
      ``ManuscriptAudit.NativeCechPointwiseCone.prepend_face_succ] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
