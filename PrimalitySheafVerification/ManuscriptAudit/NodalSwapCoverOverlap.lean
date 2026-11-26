import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Prod
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverPatch
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartOverlap

/-! The crossed nodal cover has a section after normalization and on
the actual overlap of the proper nodal charts. -/

namespace ManuscriptAudit.NodalSwapCoverOverlap

open NodalConductor NodalSwapCover NodalSwapCoverPatch
open NodalYChartOverlap (parameterRing)

noncomputable section

universe u

variable (K : Type u) [Field K]

/-- Choose the first sheet after pulling back to the polynomial normalization. -/
def normalizationSection : Cover K →ₐ[coordinates K] Polynomial K :=
  (AlgHom.fst (coordinates K) (Polynomial K) (Polynomial K)).comp (polynomialProjection K)

theorem normalizationSection_apply (g : Cover K) :
    normalizationSection K g = (g : Polynomial K × Polynomial K).1 := rfl

/-- The normalized overlap is an algebra over the original affine node. -/
def parameterAlgebra : Algebra (coordinates K) (parameterRing K) :=
  ((algebraMap (Polynomial K) (parameterRing K)).comp (coordinates K).val.toRingHom).toAlgebra

attribute [local instance] parameterAlgebra

/-- The same chosen sheet on the geometric overlap ring. -/
def overlapSection : Cover K →ₐ[coordinates K] parameterRing K where
  toRingHom := (algebraMap (Polynomial K) (parameterRing K)).comp
    (normalizationSection K).toRingHom
  commutes' a := congrArg (algebraMap (Polynomial K) (parameterRing K))
    ((normalizationSection K).commutes a)

theorem overlapSection_apply (g : Cover K) :
    overlapSection K g = algebraMap (Polynomial K) (parameterRing K)
      ((g : Polynomial K × Polynomial K).1) := rfl

end
end ManuscriptAudit.NodalSwapCoverOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSwapCoverOverlap.normalizationSection_apply,
      ``ManuscriptAudit.NodalSwapCoverOverlap.overlapSection_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
