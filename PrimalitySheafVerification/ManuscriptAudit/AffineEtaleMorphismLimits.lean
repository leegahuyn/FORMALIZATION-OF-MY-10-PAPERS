import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.MorphismProperty.CommaSites
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphism

/-!
# Left exact and continuous affine étale base change

An affine étale site of an affine scheme has finite limits.
The inclusion into the full étale site preserves these and detects
covers. The actual affine base-change functor is consequently left
exact and continuous.
-/

namespace ManuscriptAudit.AffineEtaleMorphism

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] hasFiniteLimits_of_hasTerminal_and_pullbacks
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks

private def affineTerminal (R : CommRingCat.{u}) : (Spec R).AffineEtale :=
  Scheme.AffineEtale.mk (𝟙 (Spec R))

private def imageTerminal (R : CommRingCat.{u}) :
    IsTerminal ((Scheme.AffineEtale.Spec (Spec R)).obj (affineTerminal R)) :=
  MorphismProperty.Over.mkIdTerminal @Etale (Spec R)

private def affineTerminal_isTerminal (R : CommRingCat.{u}) : IsTerminal (affineTerminal R) :=
  IsTerminal.isTerminalOfObj (Scheme.AffineEtale.Spec (Spec R)) (affineTerminal R) (imageTerminal R)

/-- The affine étale site of a spectrum has finite limits. -/
theorem spec_hasFiniteLimits (R : CommRingCat.{u}) : HasFiniteLimits (Spec R).AffineEtale := by
  letI := (affineTerminal_isTerminal R).hasTerminal
  infer_instance

/-- The affine-site inclusion over an affine scheme preserves finite limits. -/
theorem spec_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (Scheme.AffineEtale.Spec (Spec R)) := by
  let X := Spec R
  let G := Scheme.AffineEtale.Spec X
  letI : HasTerminal X.AffineEtale := (affineTerminal_isTerminal R).hasTerminal
  letI : PreservesLimit (Functor.empty.{0} X.AffineEtale) G :=
    preservesTerminal_of_iso G (G.mapIso (terminalIsTerminal.uniqueUpToIso (affineTerminal_isTerminal R)) ≪≫
      (imageTerminal R).uniqueUpToIso terminalIsTerminal)
  letI : PreservesLimitsOfShape WalkingCospan G :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (MorphismProperty.CostructuredArrow.toOver @Etale Scheme.Spec X))
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks G

variable (R S : CommRingCat.{u}) (f : Spec S ⟶ Spec R)

/-- The native affine base change between spectra preserves finite limits. -/
theorem baseChange_preservesFiniteLimits : PreservesFiniteLimits (baseChange f) := by
  let G := Scheme.AffineEtale.Spec (Spec S)
  let F := Scheme.AffineEtale.Spec (Spec R)
  let H := SmallEtaleBaseChange.etaleBaseChange f
  letI : PreservesFiniteLimits F := spec_preservesFiniteLimits R
  letI : PreservesFiniteLimits H := SmallEtaleBaseChange.preservesFiniteLimits f
  letI : PreservesFiniteLimits (baseChange f ⋙ G) :=
    preservesFiniteLimits_of_natIso (baseChangeSpecIso f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (baseChange f) G

/-- The native affine base change preserves covering sieves. -/
theorem baseChange_coverPreserving :
    CoverPreserving (Scheme.AffineEtale.topology (Spec R))
      (Scheme.AffineEtale.topology (Spec S)) (baseChange f) where
  cover_preserve {U T} hT := by
    let G := Scheme.AffineEtale.Spec (Spec S)
    let F := Scheme.AffineEtale.Spec (Spec R)
    let H := SmallEtaleBaseChange.etaleBaseChange f
    let K := (Spec S).smallEtaleTopology
    let e := baseChangeSpecIso f
    have hF : T.functorPushforward F ∈ (Spec R).smallEtaleTopology (F.obj U) :=
      (Functor.IsDenseSubsite.coverPreserving (Scheme.AffineEtale.topology (Spec R))
        (Spec R).smallEtaleTopology F).cover_preserve hT
    have hG : T.functorPushforward (F ⋙ H) ∈ K ((F ⋙ H).obj U) := by
      rw [Sieve.functorPushforward_comp]
      exact (SmallEtaleBaseChange.coverPreserving f).cover_preserve hF
    apply (G.functorPushforward_mem_iff (Scheme.AffineEtale.topology (Spec S)) K).mp
    rw [← Sieve.functorPushforward_comp]
    apply K.superset_covering _ (K.pullback_stable (e.hom.app U) hG)
    intro V k hk
    obtain ⟨W, g, a, hg, ha⟩ := hk
    refine ⟨W, g, a ≫ e.inv.app W, hg, ?_⟩
    calc
      k = (k ≫ e.hom.app U) ≫ e.inv.app U := by simp
      _ = (a ≫ (F ⋙ H).map g) ≫ e.inv.app U := by rw [ha]
      _ = _ := by
        simp only [Category.assoc]
        exact congrArg (fun b ↦ a ≫ b) (e.inv.naturality g)

/-- The native affine base change is continuous. -/
theorem baseChange_isContinuous :
    (baseChange f).IsContinuous (Scheme.AffineEtale.topology (Spec R))
      (Scheme.AffineEtale.topology (Spec S)) := by
  letI := spec_hasFiniteLimits R
  letI := baseChange_preservesFiniteLimits R S f
  letI := flat_of_preservesFiniteLimits (baseChange f)
  exact (Functor.isContinuous_iff_coverPreserving).2 (baseChange_coverPreserving R S f)

end

end ManuscriptAudit.AffineEtaleMorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleMorphism.spec_preservesFiniteLimits,
      ``ManuscriptAudit.AffineEtaleMorphism.baseChange_preservesFiniteLimits,
      ``ManuscriptAudit.AffineEtaleMorphism.baseChange_isContinuous] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
