import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-! A product chart pulls the relative diagonal back to the intersection
of the original two charts. This lemma is categorical. -/

namespace ManuscriptAudit.TwoChartDiagonal

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {X S A B : C} (f : X ⟶ S) (i : A ⟶ X) (j : B ⟶ X)

abbrev productChart : pullback (i ≫ f) (j ≫ f) ⟶ pullback f f :=
  pullback.map _ _ _ _ i j (𝟙 _) (Category.comp_id _) (Category.comp_id _)

def intersectionToProduct : pullback i j ⟶ pullback (i ≫ f) (j ≫ f) :=
  pullback.lift (pullback.fst i j) (pullback.snd i j) (by
    simp only [← Category.assoc, pullback.condition])

private theorem diagram_commutes :
    intersectionToProduct f i j ≫ productChart f i j =
      (pullback.fst i j ≫ i) ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · simp [intersectionToProduct]
  · simpa [intersectionToProduct, Category.assoc] using (pullback.condition (f := i) (g := j)).symm

private theorem cone_fst {f' : X ⟶ S} {i' : A ⟶ X} {j' : B ⟶ X}
    (T : PullbackCone (productChart f' i' j') (pullback.diagonal f')) :
    T.fst ≫ pullback.fst (i' ≫ f') (j' ≫ f') ≫ i' = T.snd := by
  have h := congrArg (fun g => g ≫ pullback.fst f' f') T.condition
  simpa only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id] using h

private theorem cone_snd {f' : X ⟶ S} {i' : A ⟶ X} {j' : B ⟶ X}
    (T : PullbackCone (productChart f' i' j') (pullback.diagonal f')) :
    T.fst ≫ pullback.snd (i' ≫ f') (j' ≫ f') ≫ j' = T.snd := by
  have h := congrArg (fun g => g ≫ pullback.snd f' f') T.condition
  simpa only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id] using h

private def witness (T : PullbackCone (productChart f i j) (pullback.diagonal f)) :
    T.pt ⟶ pullback i j :=
  pullback.lift (T.fst ≫ pullback.fst _ _) (T.fst ≫ pullback.snd _ _) (by
    rw [Category.assoc, Category.assoc, cone_fst, cone_snd])

/-- Pulling back the diagonal to the product of the two charts gives
exactly their intersection over the original space. -/
theorem square_isPullback :
    IsPullback (intersectionToProduct f i j) (pullback.fst i j ≫ i)
      (productChart f i j) (pullback.diagonal f) := by
  apply IsPullback.of_isLimit
  refine PullbackCone.IsLimit.mk (diagram_commutes f i j) (witness f i j) ?_ ?_ ?_
  · intro T
    apply pullback.hom_ext
    · simp [intersectionToProduct, witness]
    · simp [intersectionToProduct, witness]
  · intro T
    rw [← Category.assoc, witness, pullback.lift_fst, Category.assoc, cone_fst]
  · intro T m h _
    apply pullback.hom_ext
    · have h' := congrArg (fun g => g ≫ pullback.fst (i ≫ f) (j ≫ f)) h
      simpa [Category.assoc, intersectionToProduct, witness] using h'
    · have h' := congrArg (fun g => g ≫ pullback.snd (i ≫ f) (j ≫ f)) h
      simpa [Category.assoc, intersectionToProduct, witness] using h'

end
end ManuscriptAudit.TwoChartDiagonal

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwoChartDiagonal.square_isPullback
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
