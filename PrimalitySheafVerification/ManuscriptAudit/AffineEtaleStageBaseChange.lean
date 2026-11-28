import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Maps
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCategory

/-! Base change of an actual affine stage along an intermediate
chart is a genuine relative étale stage. Its maps retain the
absolute-stage chart data exactly. -/

namespace ManuscriptAudit.AffineEtaleStageBaseChange

open AffineEtaleStageCategory (Stage hom)
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D]

/-- The genuine base-changed stage is étale over the intermediate chart. -/
def baseChangeStage (T : Stage A D) : Stage B D :=
  Stage.of B D
    (Algebra.TensorProduct.lift (Algebra.ofId B D) T.toChart (fun _ _ ↦ Commute.all _ _))

/-- The natural map from the absolute stage ring to its base change. -/
abbrev transition (T : Stage A D) : T.carrier →ₐ[A] B ⊗[A] T.carrier :=
  Algebra.TensorProduct.includeRight

/-- The original map into the chart is unchanged on composing
with the actual base change. -/
theorem factor (T : Stage A D) (x : T.carrier) :
    (baseChangeStage (B := B) T).toChart (transition (B := B) T x) = T.toChart x :=
  DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId B D) T.toChart
    (fun _ _ ↦ Commute.all _ _)) x

/-- Morphisms between absolute stages base change compatibly with
the original maps to the chart. -/
def baseChangeStageMap {T U : Stage A D} (m : T ⟶ U) :
    baseChangeStage (B := B) T ⟶ baseChangeStage (B := B) U := by
  let f : (baseChangeStage (B := B) T).carrier →ₐ[B] (baseChangeStage (B := B) U).carrier :=
    Algebra.TensorProduct.map (AlgHom.id B B) (hom m)
  refine ⟨f, ?_⟩
  apply Algebra.TensorProduct.ext'
  intro b x
  change algebraMap B D b * U.toChart (hom m x) = algebraMap B D b * T.toChart x
  rw [AffineEtaleStageCategory.hom_toChart]

end
end ManuscriptAudit.AffineEtaleStageBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageBaseChange.factor,
      ``ManuscriptAudit.AffineEtaleStageBaseChange.baseChangeStageMap] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
