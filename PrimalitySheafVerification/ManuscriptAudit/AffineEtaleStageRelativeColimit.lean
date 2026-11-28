import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageColimit

/-! An actual chart which is a filtered union of affine étale
stages over the base has relative affine étale stages over any
intermediate actual weakly étale chart. -/

namespace ManuscriptAudit.AffineEtaleStageRelativeColimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open scoped TensorProduct

noncomputable section

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D]

/-- Tensoring an actual stage with the intermediate coordinate ring
preserves all specified lifts. -/
theorem relative_approximation (hA : FiniteTupleApproximation A D) :
    FiniteTupleApproximation B D := by
  intro ι _ w
  obtain ⟨C, hR, hAlg, hEt, f, hf⟩ := hA w
  letI : CommRing C := hR
  letI : Algebra A C := hAlg
  letI : Algebra.Etale A C := hEt
  let E := B ⊗[A] C
  let g : E →ₐ[B] D :=
    Algebra.TensorProduct.lift (Algebra.ofId B D) f (fun _ _ ↦ Commute.all _ _)
  refine ⟨E, inferInstance, inferInstance, inferInstance, g, fun i ↦ ?_⟩
  obtain ⟨x, hx⟩ := hf i
  refine ⟨(1 : B) ⊗ₜ[A] x, ?_⟩
  change Algebra.TensorProduct.lift (Algebra.ofId B D) f (fun _ _ ↦ Commute.all _ _)
    ((1 : B) ⊗ₜ[A] x) = w i
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, hx]

/-- The actual upper chart is a colimit of the genuine stages over
the intermediate chart, given its finite tuple approximation over the base. -/
def relative_isColimit [WeaklyEtale (structureMap B D)]
    (hA : FiniteTupleApproximation A D) :
    IsColimit (AffineEtaleStageCategory.chartCocone (A := B) (B := D)) :=
  AffineEtaleStageColimit.isColimit_chart (relative_approximation (B := B) hA)

end
end ManuscriptAudit.AffineEtaleStageRelativeColimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageRelativeColimit.relative_approximation,
      ``ManuscriptAudit.AffineEtaleStageRelativeColimit.relative_isColimit] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
