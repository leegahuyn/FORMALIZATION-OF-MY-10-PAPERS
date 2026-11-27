import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBaseChange
import PrimalitySheafVerification.ManuscriptAudit.ProetaleResidueSheaves

/-! The actual pro-étale direct images of continuous coefficient
sheaves admit explicit pullback maps on all weakly étale charts. -/

namespace ManuscriptAudit.ProetaleContinuousDirectImageMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleResidueSheaves (continuousCoefficients)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Scheme.{0}} {p : Y ⟶ Z} {q : X ⟶ Z}

/-- The actual map between two scheme pullbacks along a common chart. -/
def pullbackMap {W : Scheme.{0}} (a : W ⟶ Z) (g : X ⟶ Y) (hg : g ≫ p = q) :
    pullback a q ⟶ pullback a p :=
  pullback.lift (pullback.fst a q) (pullback.snd a q ≫ g)
    (by rw [Category.assoc, hg, pullback.condition])

@[reassoc (attr := simp)]
theorem pullbackMap_fst {W : Scheme.{0}} (a : W ⟶ Z) (g : X ⟶ Y) (hg : g ≫ p = q) :
    pullbackMap a g hg ≫ pullback.fst a p = pullback.fst a q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackMap_snd {W : Scheme.{0}} (a : W ⟶ Z) (g : X ⟶ Y) (hg : g ≫ p = q) :
    pullbackMap a g hg ≫ pullback.snd a p = pullback.snd a q ≫ g :=
  pullback.lift_snd _ _ _

/-- The square for the branch map and the pullback projections is cartesian. -/
theorem pullbackMap_isPullback {W : Scheme.{0}} (a : W ⟶ Z)
    (g : X ⟶ Y) (hg : g ≫ p = q) :
    IsPullback (pullbackMap a g hg) (pullback.snd a q) (pullback.snd a p) g := by
  have h : IsPullback (pullbackMap a g hg ≫ pullback.fst a p) (pullback.snd a q) a (g ≫ p) := by
    rw [pullbackMap_fst, hg]
    exact IsPullback.of_hasPullback a q
  exact h.of_right (pullbackMap_snd a g hg) (IsPullback.of_hasPullback a p)

private theorem pullbackMap_natural (g : X ⟶ Y) (hg : g ≫ p = q)
    {U V : Z.ProEt} (f : U ⟶ V) :
    pullbackMap U.hom g hg ≫ ((baseChange p).map f).left =
      ((baseChange q).map f).left ≫ pullbackMap V.hom g hg := by
  apply pullback.hom_ext
  · simp only [pullbackMap, baseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [pullbackMap, baseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

abbrev functions (T : Scheme.{0}) :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{1}).obj (continuousCoefficients T M)

abbrev functionsOver {T B : Scheme.{0}} (f : T ⟶ B) :=
  (directImage f AddCommGrpCat.{1}).obj (functions M T)

private def continuousPrecomp {T S : Scheme.{0}} (f : T ⟶ S) :
    ULift.{1} (C(S, M)) →+ ULift.{1} (C(T, M)) where
  toFun a := ⟨a.down.comp ⟨f, f.continuous⟩⟩
  map_zero' := by apply ULift.ext; exact ContinuousMap.ext (fun _ ↦ rfl)
  map_add' _ _ := by apply ULift.ext; exact ContinuousMap.ext (fun _ ↦ rfl)

/-- The actual diagonal map pulls a local function back to the total scheme. -/
def diagonal (p : Y ⟶ Z) : functions M Z ⟶ functionsOver M p :=
  ⟨{ app U := AddCommGrpCat.ofHom (continuousPrecomp M (pullback.fst U.unop.hom p))
     naturality := by
       intro U V f
       apply ConcreteCategory.hom_ext
       intro c
       apply ULift.ext
       apply ContinuousMap.ext
       intro x
       let c' : C(U.unop.left, M) := c.down
       change c' ((pullback.fst V.unop.hom p ≫ f.unop.left) x) =
         c' ((((baseChange p).map f.unop).left ≫ pullback.fst U.unop.hom p) x)
       simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst] <;> rfl }⟩

/-- Actual pullback of functions along a map over the common base. -/
def restriction (g : X ⟶ Y) (hg : g ≫ p = q) : functionsOver M p ⟶ functionsOver M q :=
  ⟨{ app U := AddCommGrpCat.ofHom (continuousPrecomp M (pullbackMap U.unop.hom g hg))
     naturality := by
       intro U V f
       apply ConcreteCategory.hom_ext
       intro c
       apply ULift.ext
       apply ContinuousMap.ext
       intro x
       let c' : C(((baseChange p).obj U.unop).left, M) := c.down
       change c' ((pullbackMap V.unop.hom g hg ≫ ((baseChange p).map f.unop).left) x) =
         c' ((((baseChange q).map f.unop).left ≫ pullbackMap U.unop.hom g hg) x)
       rw [pullbackMap_natural] }⟩

/-- A function pulled back from the base gives the same local value along every branch. -/
theorem diagonal_restriction (g : X ⟶ Y) (hg : g ≫ p = q) :
    diagonal M p ≫ restriction M g hg = diagonal M q := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  let c' : C(U.unop.left, M) := c.down
  change c' ((pullbackMap U.unop.hom g hg ≫ pullback.fst U.unop.hom p) x) =
    c' (pullback.fst U.unop.hom q x)
  rw [pullbackMap_fst]

end
end ManuscriptAudit.ProetaleContinuousDirectImageMaps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleContinuousDirectImageMaps.pullbackMap_isPullback,
      ``ManuscriptAudit.ProetaleContinuousDirectImageMaps.diagonal_restriction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
