import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-!
# Restricting to an arbitrary étale object

Postcomposition along an étale morphism preserves pullback squares
and covering families. The resulting restriction of actual sheaves
is both left exact and left adjoint to the native direct image.
-/

namespace ManuscriptAudit.EtaleObjectRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem compatiblePreserving_of_pullbacks {C D : Type*} [Category* C] [Category* D]
    [HasPullbacks C] (J : GrothendieckTopology D) (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] : CompatiblePreserving.{w} J F where
  compatible P Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h := by
    let a := pullback.fst g₁ g₂
    let b := pullback.snd g₁ g₂
    let he := (IsPullback.of_hasPullback g₁ g₂).map F
    let r := he.lift f₁ f₂ h
    have hv : P.obj.map (F.map a).op (x g₁ hg₁) =
        P.obj.map (F.map b).op (x g₂ hg₂) :=
      hx a b hg₁ hg₂ pullback.condition
    rw [← he.lift_fst f₁ f₂ h, ← he.lift_snd f₁ f₂ h]
    simp only [op_comp, Functor.map_comp, types_comp_apply]
    exact congrArg (P.obj.map r.op) hv

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Postcomposition along an étale morphism on the native small site. -/
abbrev postcompose : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (show Etale j from inferInstance)

/-- This postcomposition preserves the actual covering families. -/
theorem postcompose_coverPreserving :
    CoverPreserving U.smallEtaleTopology X.smallEtaleTopology (postcompose j) where
  cover_preserve {_ S} hS := by
    obtain ⟨ι, Z, f, rfl⟩ := Sieve.exists_eq_ofArrows S
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
    rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    change (⋃ i, Set.range (f i).left) = Set.univ
    exact hS

/-- The postcomposition functor preserves the native pullbacks of étale objects. -/
theorem postcompose_preservesPullbacks : PreservesLimitsOfShape WalkingCospan (postcompose j) := by
  let F := Scheme.Etale.forget X ⋙ Over.forget X
  letI : PreservesLimitsOfShape WalkingCospan (postcompose j ⋙ F) := by
    change PreservesLimitsOfShape WalkingCospan (Scheme.Etale.forget U ⋙ Over.forget U)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (postcompose j) F

/-- The functor defining restriction to an étale object is continuous. -/
theorem postcompose_isContinuous :
    (postcompose j).IsContinuous U.smallEtaleTopology X.smallEtaleTopology := by
  letI := postcompose_preservesPullbacks j
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_of_pullbacks X.smallEtaleTopology (postcompose j))
    (postcompose_coverPreserving j)

private abbrev A := AddCommGrpCat.{u}

/-- Native restriction of abelian sheaves to an étale object. -/
def restriction : Sheaf X.smallEtaleTopology A.{u} ⥤ Sheaf U.smallEtaleTopology A.{u} :=
  letI := postcompose_isContinuous j
  (postcompose j).sheafPushforwardContinuous A.{u} U.smallEtaleTopology X.smallEtaleTopology

/-- Actual restriction is left adjoint to the native direct image. -/
def restrictionAdjunction : restriction j ⊣ SmallEtaleBaseChange.directImage j A.{u} := by
  letI := postcompose_isContinuous j
  letI := SmallEtaleBaseChange.isContinuous_of_baseChange j
  let a : postcompose j ⊣ SmallEtaleBaseChange.etaleBaseChange j :=
    MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ j
      (show Etale j from inferInstance) trivial
  exact a.sheafPushforwardContinuous (E := A.{u}) U.smallEtaleTopology X.smallEtaleTopology

/-- Actual restriction preserves finite limits. -/
theorem restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction j) := by
  let F := sheafToPresheaf U.smallEtaleTopology A.{u}
  let G := sheafToPresheaf X.smallEtaleTopology A.{u}
  let P := (Functor.whiskeringLeft U.Etaleᵒᵖ X.Etaleᵒᵖ A.{u}).obj (postcompose j).op
  letI : PreservesFiniteLimits (restriction j ⋙ F) := by
    change PreservesFiniteLimits (G ⋙ P)
    exact comp_preservesFiniteLimits G P
  exact preservesFiniteLimits_of_reflects_of_preserves (restriction j) F

/-- The unit sheaf restricts to the actual unit sheaf of the étale scheme. -/
def restrictionUnitsIso {U X : Scheme.{0}} (j : U ⟶ X) [Etale j] :
    (restriction j).obj (KummerUnitsSheaf.fullCoordinateUnitSheaf X) ≅
      KummerUnitsSheaf.fullCoordinateUnitSheaf U :=
  (fullyFaithfulSheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{0}).preimageIso (Iso.refl _)

end

end ManuscriptAudit.EtaleObjectRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleObjectRestriction.postcompose_isContinuous,
      ``ManuscriptAudit.EtaleObjectRestriction.restrictionAdjunction,
      ``ManuscriptAudit.EtaleObjectRestriction.restriction_preservesFiniteLimits,
      ``ManuscriptAudit.EtaleObjectRestriction.restrictionUnitsIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
