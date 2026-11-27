import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! Base change along any scheme morphism acts on the native pro-étale
site and preserves covering sieves. -/

namespace ManuscriptAudit.ProetaleBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual pullback of weakly étale objects. -/
abbrev baseChange : Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

instance preservesFiniteLimits : PreservesFiniteLimits (baseChange f) := by
  let ex := Scheme.ProEt.forget X
  let ey := Scheme.ProEt.forget Y
  letI : PreservesFiniteLimits (ey ⋙ Over.pullback f) := comp_preservesFiniteLimits _ _
  let c : baseChange f ⋙ ex ≅ ey ⋙ Over.pullback f :=
    MorphismProperty.Over.pullbackCompForgetIso (P := @WeaklyEtale) (Q := ⊤) f
  letI := preservesFiniteLimits_of_natIso c.symm
  exact preservesFiniteLimits_of_reflects_of_preserves (baseChange f) ex

private theorem pullback_map_isPullback {A B : Y.ProEt} (g : A ⟶ B) :
    IsPullback ((baseChange f).map g).left (pullback.fst A.hom f)
      (pullback.fst B.hom f) g.left := by
  have hSnd : ((baseChange f).map g).left ≫ pullback.snd B.hom f = pullback.snd A.hom f := by
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
  have hFst : ((baseChange f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  refine IsPullback.of_right ?_ hFst (IsPullback.of_hasPullback B.hom f).flip
  rw [hSnd, MorphismProperty.Over.w g]
  exact (IsPullback.of_hasPullback A.hom f).flip

set_option maxHeartbeats 800000 in
/-- The actual weakly-étale fpqc covering sieves are preserved by base change. -/
theorem coverPreserving : CoverPreserving (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (baseChange f) where
  cover_preserve {B S} hS := by
    let F := baseChange f
    let G := Scheme.ProEt.forget Y ⋙ Over.forget Y
    let H := Scheme.ProEt.forget X ⋙ Over.forget X
    let J := Scheme.ProEt.precoverage Y
    letI : J.IsStableUnderComposition := by
      change (Scheme.proetalePrecoverage.comap G).IsStableUnderComposition
      infer_instance
    letI : J.IsStableUnderBaseChange := by
      change (Scheme.proetalePrecoverage.comap G).IsStableUnderBaseChange
      infer_instance
    letI : J.HasIsos := by
      change (Scheme.proetalePrecoverage.comap G).HasIsos
      infer_instance
    obtain ⟨P, hP, hPS⟩ := (J.mem_toGrothendieck_iff_of_isStableUnderComposition).mp hS
    have h₀ : P.map G ∈ Scheme.proetalePrecoverage B.left := hP
    have h₁ : P.map F ∈ Scheme.ProEt.precoverage X (F.obj B) := by
      change (P.map F).map H ∈ Scheme.proetalePrecoverage (pullback B.hom f)
      obtain ⟨ι, A, g, rfl⟩ := P.exists_eq_ofArrows
      rw [Presieve.map_ofArrows] at h₀
      rw [Presieve.map_ofArrows, Presieve.map_ofArrows]
      exact Precoverage.mem_coverings_of_isPullback (fun i ↦ (g i).left) h₀
        (pullback.fst B.hom f) (fun i ↦ (F.map (g i)).left)
        (fun i ↦ pullback.fst (A i).hom f) (fun i ↦ pullback_map_isPullback f (g i))
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck h₁)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨hg⟩
    exact Sieve.image_mem_functorPushforward _ _ (hPS _ _ hg)

instance continuous :
    (baseChange f).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  by
    letI := flat_of_preservesFiniteLimits (baseChange f)
    exact (Functor.isContinuous_iff_coverPreserving).mpr (coverPreserving f)

/-- The actual small pro-étale direct image along a scheme morphism. -/
def directImage (A : Type v) [Category.{w} A] :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology Y) A :=
  (baseChange f).sheafPushforwardContinuous A _ _

end
end ManuscriptAudit.ProetaleBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleBaseChange.preservesFiniteLimits,
      ``ManuscriptAudit.ProetaleBaseChange.coverPreserving,
      ``ManuscriptAudit.ProetaleBaseChange.continuous] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
