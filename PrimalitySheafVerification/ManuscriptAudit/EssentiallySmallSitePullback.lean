import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Left-exact inverse image for essentially small sites

The inverse image on abelian sheaves is computed on native small
models of the two site categories. Transport through the equivalences
identifies its right adjoint with the original, actual direct image.
-/

namespace ManuscriptAudit.EssentiallySmallSitePullback

open CategoryTheory CategoryTheory.Limits

universe u u₁ v₁ u₂ v₂

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u} C]
  {D : Type u₂} [Category.{v₂} D] [EssentiallySmall.{u} D]

private abbrev modelEquiv (T : Type*) [Category* T] [EssentiallySmall.{u} T] :=
  equivSmallModel.{u} T

private abbrev modelTopology {T : Type*} [Category* T] [EssentiallySmall.{u} T]
    (J : GrothendieckTopology T) :=
  (modelEquiv.{u} T).inverse.inducedTopology J

private abbrev modelFunctor (G : C ⥤ D) : SmallModel.{u} C ⥤ SmallModel.{u} D :=
  (modelEquiv.{u} C).inverse ⋙ G ⋙ (modelEquiv.{u} D).functor

private def modelFunctorIso (G : C ⥤ D) :
    (modelEquiv.{u} C).functor ⋙ modelFunctor G ⋙ (modelEquiv.{u} D).inverse ≅ G := by
  let E := modelEquiv.{u} C
  let F := modelEquiv.{u} D
  let e : modelFunctor G ⋙ F.inverse ≅ E.inverse ⋙ G :=
    Functor.associator E.inverse (G ⋙ F.functor) F.inverse ≪≫
      Functor.isoWhiskerLeft E.inverse
        (Functor.associator G F.functor F.inverse ≪≫
          Functor.isoWhiskerLeft G F.unitIso.symm ≪≫ G.rightUnitor)
  exact Functor.isoWhiskerLeft E.functor e ≪≫
    (Functor.associator E.functor E.inverse G).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm G ≪≫ G.leftUnitor

private abbrev A := AddCommGrpCat.{u}

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) [G.IsContinuous J K]

set_option maxHeartbeats 3000000 in
/-- Continuous left-exact functors between essentially small sites have an
actual abelian inverse image preserving finite limits. -/
theorem exists_leftExactLeftAdjoint [HasFiniteLimits C] [PreservesFiniteLimits G] :
    ∃ L : Sheaf J A.{u} ⥤ Sheaf K A.{u},
      Nonempty (L ⊣ G.sheafPushforwardContinuous A.{u} J K) ∧ PreservesFiniteLimits L := by
  let E := modelEquiv.{u} C
  let F := modelEquiv.{u} D
  let J' := modelTopology.{u} J
  let K' := modelTopology.{u} K
  let g := modelFunctor G
  letI : F.functor.IsContinuous K K' := inferInstance
  letI : E.inverse.IsContinuous J' J := inferInstance
  letI : E.functor.IsContinuous J J' := inferInstance
  letI : F.inverse.IsContinuous K' K := inferInstance
  letI : (G ⋙ F.functor).IsContinuous J K' := Functor.isContinuous_comp G F.functor J K K'
  letI : g.IsContinuous J' K' := Functor.isContinuous_comp E.inverse (G ⋙ F.functor) J' J K'
  letI : HasFiniteLimits (SmallModel.{u} C) :=
    ⟨fun L _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.inverse⟩
  letI : PreservesFiniteLimits g := by
    change PreservesFiniteLimits (E.inverse ⋙ G ⋙ F.functor)
    letI : PreservesFiniteLimits (G ⋙ F.functor) := comp_preservesFiniteLimits G F.functor
    exact comp_preservesFiniteLimits E.inverse (G ⋙ F.functor)
  letI : RepresentablyFlat g := flat_of_preservesFiniteLimits g
  let R₀ := g.sheafPushforwardContinuous A.{u} J' K'
  let R₁ := F.inverse.sheafPushforwardContinuous A.{u} K' K
  let R₂ := E.functor.sheafPushforwardContinuous A.{u} J J'
  letI : R₁.IsEquivalence :=
    inferInstanceAs ((F.sheafCongr K K' A.{u}).functor.IsEquivalence)
  letI : R₂.IsEquivalence :=
    inferInstanceAs ((E.sheafCongr J J' A.{u}).inverse.IsEquivalence)
  letI : HasSheafify K' A.{u} := inferInstance
  letI : ∀ P : (SmallModel.{u} C)ᵒᵖ ⥤ A.{u}, g.op.HasLeftKanExtension P :=
    fun _ ↦ inferInstance
  letI : R₀.IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous g A.{u} J' K').isRightAdjoint
  let L₀ := g.sheafPullback A.{u} J' K'
  let L₁ := R₁.asEquivalence.inverse
  let L₂ := R₂.asEquivalence.inverse
  letI : PreservesFiniteLimits L₀ := by
    change PreservesFiniteLimits (g.sheafPullback A.{u} J' K')
    infer_instance
  letI := Functor.isContinuous_comp g F.inverse J' K' K
  letI := Functor.isContinuous_comp E.functor (g ⋙ F.inverse) J J' K
  let e₁ : R₁ ⋙ R₀ ≅ (g ⋙ F.inverse).sheafPushforwardContinuous A.{u} J' K :=
    Functor.sheafPushforwardContinuousComp (F := g) (G := F.inverse)
      (A := A.{u}) (J := J') (K := K') (L := K)
  let e₂ : R₁ ⋙ R₀ ⋙ R₂ ≅ G.sheafPushforwardContinuous A.{u} J K :=
    (Functor.associator R₁ R₀ R₂).symm ≪≫
      Functor.isoWhiskerRight e₁ R₂ ≪≫
      Functor.sheafPushforwardContinuousComp (F := E.functor) (G := g ⋙ F.inverse)
        (A := A.{u}) (J := J) (K := J') (L := K) ≪≫
      Functor.sheafPushforwardContinuousIso (modelFunctorIso G)
        (A := A.{u}) (J := J) (K := K)
  let L := (L₂ ⋙ L₀) ⋙ L₁
  let a₀ : L₀ ⊣ R₀ := g.sheafAdjunctionContinuous A.{u} J' K'
  let a₁ : L₁ ⊣ R₁ := R₁.asEquivalence.symm.toAdjunction
  let a₂ : L₂ ⊣ R₂ := R₂.asEquivalence.symm.toAdjunction
  letI : PreservesFiniteLimits (L₂ ⋙ L₀) := comp_preservesFiniteLimits L₂ L₀
  exact ⟨L, ⟨((a₂.comp a₀).comp a₁).ofNatIsoRight e₂⟩,
    comp_preservesFiniteLimits (L₂ ⋙ L₀) L₁⟩

end

end ManuscriptAudit.EssentiallySmallSitePullback

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EssentiallySmallSitePullback.exists_leftExactLeftAdjoint
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
