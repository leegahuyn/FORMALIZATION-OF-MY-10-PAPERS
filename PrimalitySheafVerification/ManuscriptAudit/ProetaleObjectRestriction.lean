import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBaseChange

/-! Restriction to an arbitrary weakly étale object is left exact and
left adjoint to the actual pro-étale direct image. -/

namespace ManuscriptAudit.ProetaleObjectRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension (proetalePostcompose postcomposeCoverPreserving)
open ProetaleBaseChange (baseChange directImage)

universe u v w
noncomputable section

variable {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]

theorem postcompose_preservesPullbacks : PreservesLimitsOfShape WalkingCospan (proetalePostcompose j) := by
  let F := Scheme.ProEt.forget X ⋙ Over.forget X
  letI : PreservesLimitsOfShape WalkingCospan (proetalePostcompose j ⋙ F) := by
    change PreservesLimitsOfShape WalkingCospan (Scheme.ProEt.forget U ⋙ Over.forget U)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (proetalePostcompose j) F

theorem postcompose_isContinuous :
    (proetalePostcompose j).IsContinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) := by
  letI := postcompose_preservesPullbacks j
  exact Functor.isContinuous_of_coverPreserving
    (EtaleObjectRestriction.compatiblePreserving_of_pullbacks (Scheme.ProEt.topology X)
      (proetalePostcompose j))
    (postcomposeCoverPreserving j)

variable (A : Type v) [Category.{w} A]

def restriction : Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology U) A :=
  letI := postcompose_isContinuous j
  (proetalePostcompose j).sheafPushforwardContinuous A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

def restrictionAdjunction : restriction j A ⊣ directImage j A := by
  letI := postcompose_isContinuous j
  let a : proetalePostcompose j ⊣ baseChange j :=
    MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial
  exact a.sheafPushforwardContinuous (E := A) (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

end
end ManuscriptAudit.ProetaleObjectRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleObjectRestriction.restrictionAdjunction
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
