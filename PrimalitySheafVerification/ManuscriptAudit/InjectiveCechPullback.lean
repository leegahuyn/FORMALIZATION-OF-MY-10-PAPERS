import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import PrimalitySheafVerification.ManuscriptAudit.InjectiveCechOne

/-! A Čech cocycle on actual double and triple overlaps has a
coboundary when the sheaf is injective and the base is terminal. -/

namespace ManuscriptAudit.InjectiveCechPullback

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

noncomputable section

variable {U T : C} (f : U ⟶ T)

abbrev Double := pullback f f

abbrev first : Double f ⟶ U := pullback.fst f f

abbrev second : Double f ⟶ U := pullback.snd f f

abbrev Triple := pullback (first f) (first f)

abbrev edge12 : Triple f ⟶ Double f := pullback.fst (first f) (first f)

abbrev edge13 : Triple f ⟶ Double f := pullback.snd (first f) (first f)

/-- The face retaining the second and third vertices of the triple overlap. -/
def edge23 : Triple f ⟶ Double f :=
  pullback.lift (edge12 f ≫ second f) (edge13 f ≫ second f) (by
    simp only [Category.assoc, ← pullback.condition (f := f) (g := f)]
    rw [← Category.assoc, ← Category.assoc,
      pullback.condition (f := first f) (g := first f)])

private def tripleLift {W : C} (a b d : W ⟶ U) (hab : a ≫ f = b ≫ f)
    (had : a ≫ f = d ≫ f) : W ⟶ Triple f := by
  have h₁ : (pullback.lift a b hab : W ⟶ Double f) ≫ first f = a :=
    pullback.lift_fst a b hab
  have h₂ : (pullback.lift a d had : W ⟶ Double f) ≫ first f = a :=
    pullback.lift_fst a d had
  exact pullback.lift (pullback.lift a b hab) (pullback.lift a d had) (h₁.trans h₂.symm)

@[simp] private theorem tripleLift_edge12 {W : C} (a b d : W ⟶ U)
    (hab : a ≫ f = b ≫ f) (had : a ≫ f = d ≫ f) :
    tripleLift f a b d hab had ≫ edge12 f = pullback.lift a b hab := by
  simp only [tripleLift, pullback.lift_fst]

@[simp] private theorem tripleLift_edge13 {W : C} (a b d : W ⟶ U)
    (hab : a ≫ f = b ≫ f) (had : a ≫ f = d ≫ f) :
    tripleLift f a b d hab had ≫ edge13 f = pullback.lift a d had := by
  simp only [tripleLift, pullback.lift_snd]

private theorem tripleLift_edge23 {W : C} (a b d : W ⟶ U)
    (hab : a ≫ f = b ≫ f) (had : a ≫ f = d ≫ f) :
    tripleLift f a b d hab had ≫ edge23 f = pullback.lift b d (hab.symm.trans had) := by
  apply pullback.hom_ext
  · rw [Category.assoc, edge23, pullback.lift_fst, ← Category.assoc, tripleLift_edge12]
    simp only [pullback.lift_snd, pullback.lift_fst]
  · rw [Category.assoc, edge23, pullback.lift_snd, ← Category.assoc, tripleLift_edge13]
    simp only [pullback.lift_snd]

variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v}]

private theorem restrict_restrict (I : Sheaf J AddCommGrpCat.{v}) {A B D : C}
    (a : A ⟶ B) (b : B ⟶ D) (z : I.obj.obj (op D)) :
    I.obj.map a.op (I.obj.map b.op z) = I.obj.map (a ≫ b).op z := by
  rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]

/-- A sheaf cocycle on the double overlap of an object over a terminal
base is a coboundary if the coefficient sheaf is injective. -/
theorem exists_coboundary (hT : IsTerminal T) (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (z : I.obj.obj (op (Double f)))
    (hz : I.obj.map (edge23 f).op z - I.obj.map (edge13 f).op z +
      I.obj.map (edge12 f).op z = 0) :
    ∃ b : I.obj.obj (op U), z = I.obj.map (second f).op b - I.obj.map (first f).op b := by
  let c {W : C} (a b : W ⟶ U) : I.obj.obj (op W) :=
    I.obj.map (pullback.lift a b (hT.hom_ext _ _)).op z
  have hNat {W V : C} (r : V ⟶ W) (a b : W ⟶ U) :
      I.obj.map r.op (c a b) = c (r ≫ a) (r ≫ b) := by
    change I.obj.map r.op (I.obj.map (pullback.lift a b (hT.hom_ext _ _)).op z) =
      I.obj.map (pullback.lift (r ≫ a) (r ≫ b) (hT.hom_ext _ _)).op z
    have he : r ≫ (pullback.lift a b (hT.hom_ext _ _) : W ⟶ Double f) =
        pullback.lift (r ≫ a) (r ≫ b) (hT.hom_ext _ _) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    rw [restrict_restrict, he]
  have hCocycle {W : C} (a b d : W ⟶ U) : c b d - c a d + c a b = 0 := by
    let q := tripleLift f a b d (hT.hom_ext _ _) (hT.hom_ext _ _)
    have h := congrArg (fun x ↦ (I.obj.map q.op).hom x) hz
    rw [map_add, map_sub, map_zero] at h
    change I.obj.map q.op (I.obj.map (edge23 f).op z) -
      I.obj.map q.op (I.obj.map (edge13 f).op z) +
      I.obj.map q.op (I.obj.map (edge12 f).op z) = 0 at h
    simpa only [restrict_restrict, q, tripleLift_edge23, tripleLift_edge13, tripleLift_edge12, c] using h
  obtain ⟨b, hb⟩ := InjectiveCechOne.exists_coboundary J U I c hNat hCocycle
  refine ⟨b, ?_⟩
  have h := hb (first f) (second f)
  have he : pullback.lift (first f) (second f) (hT.hom_ext _ _) = 𝟙 (Double f) := by
    apply pullback.hom_ext <;> simp
  simpa only [c, he, op_id, I.obj.map_id, ConcreteCategory.id_apply] using h

end

end ManuscriptAudit.InjectiveCechPullback

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.InjectiveCechPullback.exists_coboundary
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
