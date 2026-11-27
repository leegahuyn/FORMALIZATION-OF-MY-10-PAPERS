import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import PrimalitySheafVerification.ManuscriptAudit.InjectiveCechPullback

/-! The first three degrees of the actual Čech nerve and their
comparison with iterated pullbacks. -/

namespace ManuscriptAudit.CechNerveLowDegrees

open CategoryTheory CategoryTheory.Limits Opposite
open InjectiveCechPullback
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [HasFiniteLimits C]
variable {U T : C} (f : U ⟶ T)

abbrev N (n : ℕ) := (Arrow.mk f).cechNerve.obj (op ⦋n⦌)

abbrev vertex (n : ℕ) (i : Fin (n + 1)) : N f n ⟶ U :=
  WidePullback.π (fun _ : Fin (n + 1) ↦ f) i

abbrev face (n : ℕ) (i : Fin (n + 2)) : N f (n + 1) ⟶ N f n :=
  (Arrow.mk f).cechNerve.map (SimplexCategory.δ i).op

@[reassoc]
theorem face_vertex (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    face f n i ≫ vertex f n k = vertex f (n + 1) ((SimplexCategory.δ i).toOrderHom k) := by
  change (Arrow.mk f).cechNerve.map (SimplexCategory.δ i).op ≫ vertex f n k = _
  rw [Arrow.cechNerve_map]
  exact WidePullback.lift_π _ _ _ _ _

/-- The canonical identification of the first nerve object with the cover. -/
def zeroIso : N f 0 ≅ U where
  hom := vertex f 0 0
  inv := WidePullback.lift f (fun _ : Fin 1 ↦ 𝟙 U) (fun _ ↦ Category.id_comp _)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, WidePullback.lift_base, WidePullback.π_arrow, Category.id_comp]
  inv_hom_id := WidePullback.lift_π _ _ _ _ _

/-- The ordered pair of vertices of a higher nerve object. -/
def pair (n : ℕ) (a b : Fin (n + 1)) : N f n ⟶ Double f :=
  pullback.lift (vertex f n a) (vertex f n b)
    ((WidePullback.π_arrow (fun _ : Fin (n + 1) ↦ f) a).trans
      (WidePullback.π_arrow (fun _ : Fin (n + 1) ↦ f) b).symm)

@[simp, reassoc]
theorem pair_first (n : ℕ) (a b : Fin (n + 1)) :
    pair f n a b ≫ first f = vertex f n a := pullback.lift_fst _ _ _

@[simp, reassoc]
theorem pair_second (n : ℕ) (a b : Fin (n + 1)) :
    pair f n a b ≫ second f = vertex f n b := pullback.lift_snd _ _ _

@[reassoc]
theorem face_pair (n : ℕ) (i : Fin (n + 2)) (a b : Fin (n + 1)) :
    face f n i ≫ pair f n a b = pair f (n + 1)
      ((SimplexCategory.δ i).toOrderHom a) ((SimplexCategory.δ i).toOrderHom b) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pair_first, face_vertex]
  · simp only [Category.assoc, pair_second, face_vertex]

/-- The iterated double pullback maps to degree one of the nerve. -/
def doubleSection : Double f ⟶ N f 1 :=
  WidePullback.lift (first f ≫ f) (fun i : Fin 2 ↦
    Fin.cases (first f) (fun _ ↦ second f) i) (fun i ↦ by
      fin_cases i
      · rfl
      · exact (pullback.condition (f := f) (g := f)).symm)

@[simp, reassoc]
theorem doubleSection_pair :
    doubleSection f ≫ pair f 1 0 1 = 𝟙 (Double f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pair_first, doubleSection, WidePullback.lift_π, Category.id_comp] <;> rfl
  · rw [Category.assoc, pair_second, doubleSection, WidePullback.lift_π, Category.id_comp] <;> rfl

/-- The degree-two nerve object maps to the iterated triple pullback. -/
def triple : N f 2 ⟶ Triple f :=
  pullback.lift (pair f 2 0 1) (pair f 2 0 2) (by simp)

@[simp, reassoc]
theorem triple_edge12 : triple f ≫ edge12 f = pair f 2 0 1 :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem triple_edge13 : triple f ≫ edge13 f = pair f 2 0 2 :=
  pullback.lift_snd _ _ _

@[simp, reassoc]
theorem triple_edge23 : triple f ≫ edge23 f = pair f 2 1 2 := by
  apply pullback.hom_ext
  · rw [Category.assoc, edge23, pullback.lift_fst, ← Category.assoc,
      triple_edge12, pair_second, pair_first]
  · rw [Category.assoc, edge23, pullback.lift_snd, ← Category.assoc,
      triple_edge13, pair_second, pair_second]

theorem face_zero_zero : face f 0 0 ≫ (zeroIso f).hom = pair f 1 0 1 ≫ second f := by
  change face f 0 0 ≫ vertex f 0 0 = _
  rw [face_vertex, pair_second] <;> rfl

theorem face_zero_one : face f 0 1 ≫ (zeroIso f).hom = pair f 1 0 1 ≫ first f := by
  change face f 0 1 ≫ vertex f 0 0 = _
  rw [face_vertex, pair_first] <;> rfl

theorem face_one_zero : face f 1 0 ≫ pair f 1 0 1 = triple f ≫ edge23 f := by
  rw [face_pair, triple_edge23] <;> rfl

theorem face_one_one : face f 1 1 ≫ pair f 1 0 1 = triple f ≫ edge13 f := by
  rw [face_pair, triple_edge13] <;> rfl

theorem face_one_two : face f 1 2 ≫ pair f 1 0 1 = triple f ≫ edge12 f := by
  rw [face_pair, triple_edge12] <;> rfl

end

end ManuscriptAudit.CechNerveLowDegrees

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CechNerveLowDegrees.zeroIso,
      ``ManuscriptAudit.CechNerveLowDegrees.doubleSection_pair,
      ``ManuscriptAudit.CechNerveLowDegrees.face_zero_zero,
      ``ManuscriptAudit.CechNerveLowDegrees.face_zero_one,
      ``ManuscriptAudit.CechNerveLowDegrees.face_one_zero,
      ``ManuscriptAudit.CechNerveLowDegrees.face_one_one,
      ``ManuscriptAudit.CechNerveLowDegrees.face_one_two] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
