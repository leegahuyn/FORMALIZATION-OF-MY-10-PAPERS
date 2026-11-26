import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf

/-! Native maps of continuous-function direct images on the small étale
site, defined by pullback of functions along the actual schemes. -/

namespace ManuscriptAudit.EtaleContinuousDirectImageMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleContinuousMapSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y Z : Scheme.{u}} {p : Y ⟶ Z} {q : X ⟶ Z}

/-- The base-changed map between two actual scheme pullbacks over Z. -/
def baseChangeMap (g : X ⟶ Y) (hg : g ≫ p = q) (U : Z.Etale) :
    ((etaleBaseChange q).obj U).left ⟶ ((etaleBaseChange p).obj U).left :=
  pullback.lift (pullback.fst U.hom q) (pullback.snd U.hom q ≫ g)
    (by rw [Category.assoc, hg, pullback.condition])

@[reassoc (attr := simp)]
theorem baseChangeMap_fst (g : X ⟶ Y) (hg : g ≫ p = q) (U : Z.Etale) :
    baseChangeMap g hg U ≫ pullback.fst U.hom p = pullback.fst U.hom q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeMap_snd (g : X ⟶ Y) (hg : g ≫ p = q) (U : Z.Etale) :
    baseChangeMap g hg U ≫ pullback.snd U.hom p = pullback.snd U.hom q ≫ g :=
  pullback.lift_snd _ _ _

private theorem baseChangeMap_natural (g : X ⟶ Y) (hg : g ≫ p = q)
    {U V : Z.Etale} (f : U ⟶ V) :
    baseChangeMap g hg U ≫ ((etaleBaseChange p).map f).left =
      ((etaleBaseChange q).map f).left ≫ baseChangeMap g hg V := by
  apply pullback.hom_ext
  · simp only [baseChangeMap, etaleBaseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [baseChangeMap, etaleBaseChange, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

variable (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M]
variable [IsTopologicalAddGroup M]

abbrev functionsOver {T B : Scheme.{u}} (f : T ⟶ B) :=
  (directImage f AddCommGrpCat.{u}).obj (continuousMapSheaf T M)

private def continuousPrecomp {T S : Scheme.{u}} (f : T ⟶ S) :
    ContinuousMap S M →+ ContinuousMap T M where
  toFun a := a.comp ⟨f, f.continuous⟩
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

/-- The actual diagonal map sends each local function to its pullback. -/
def diagonal (p : Y ⟶ Z) : continuousMapSheaf Z M ⟶ functionsOver M p :=
  ⟨{ app U := AddCommGrpCat.ofHom (continuousPrecomp M (pullback.fst U.unop.hom p))
     naturality := by
       intro U V f
       apply ConcreteCategory.hom_ext
       intro c
       apply ContinuousMap.ext
       intro x
       let c' : ContinuousMap U.unop.left M := c
       change c' ((pullback.fst V.unop.hom p ≫ f.unop.left) x) =
         c' ((((etaleBaseChange p).map f.unop).left ≫ pullback.fst U.unop.hom p) x)
       simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst] }⟩

/-- Pullback of local functions along a scheme map over the common base. -/
def restriction (g : X ⟶ Y) (hg : g ≫ p = q) : functionsOver M p ⟶ functionsOver M q :=
  ⟨{ app U := AddCommGrpCat.ofHom (continuousPrecomp M (baseChangeMap g hg U.unop))
     naturality := by
       intro U V f
       apply ConcreteCategory.hom_ext
       intro c
       apply ContinuousMap.ext
       intro x
       let c' : ContinuousMap ((etaleBaseChange p).obj U.unop).left M := c
       change c' ((baseChangeMap g hg V.unop ≫ ((etaleBaseChange p).map f.unop).left) x) =
         c' ((((etaleBaseChange q).map f.unop).left ≫ baseChangeMap g hg U.unop) x)
       rw [baseChangeMap_natural] }⟩

/-- A function pulled back from the base gives the same local value on
any specified branch over that base. -/
theorem diagonal_restriction (g : X ⟶ Y) (hg : g ≫ p = q) :
    diagonal M p ≫ restriction M g hg = diagonal M q := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro c
  apply ContinuousMap.ext
  intro x
  let c' : ContinuousMap U.unop.left M := c
  change c' ((baseChangeMap g hg U.unop ≫ pullback.fst U.unop.hom p) x) =
    c' (pullback.fst U.unop.hom q x)
  rw [baseChangeMap_fst]

end
end ManuscriptAudit.EtaleContinuousDirectImageMaps

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleContinuousDirectImageMaps.diagonal_restriction
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
