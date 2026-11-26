import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineSingular
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveClosure
import PrimalitySheafVerification.ManuscriptAudit.NodalAwayNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartImmersion

/-! The actual nodal curve is singular, while the affine complement of
its conductor and the entire Y-chart have smooth coordinate algebras. -/

namespace ManuscriptAudit.NodalSmoothCharts

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (affineOpen affineOpen_toBase projectiveNodeToBase)
open NodalAffineSingular (affineNode_not_smooth)
open NodalConductor (coordinates x)
open NodalAwayNormalization (nodeX normalizationEquiv)
open NodalYChartImmersion (yCoordinateRing coordinateEquiv)

noncomputable section

universe u
variable (K : Type u) [Field K]

private theorem localizedPolynomial_smooth (f : Polynomial K) :
    Algebra.Smooth K (Localization.Away f) := by
  letI : Algebra.Smooth K (Polynomial K) := ⟨inferInstance, inferInstance⟩
  letI : Algebra.Smooth (Polynomial K) (Localization.Away f) :=
    Algebra.Smooth.of_isLocalization_Away f
  exact Algebra.Smooth.comp K (Polynomial K) (Localization.Away f)

/-- The coordinate ring of the actual punctured Z-chart is smooth. -/
theorem puncturedAffineAlgebra_smooth : Algebra.Smooth K (Localization.Away (nodeX K)) := by
  letI := localizedPolynomial_smooth K (x K)
  exact Algebra.Smooth.of_equiv (normalizationEquiv K).symm

/-- The coordinate ring of the actual Y-chart is smooth. -/
theorem yChartAlgebra_smooth : Algebra.Smooth K (yCoordinateRing K) := by
  letI := localizedPolynomial_smooth K ((1 : Polynomial K) - Polynomial.X ^ 2)
  exact Algebra.Smooth.of_equiv ((coordinateEquiv K).restrictScalars K).symm

/-- The actual proper nodal curve is not smooth over K. -/
theorem projectiveNode_not_smooth : ¬ AlgebraicGeometry.Smooth (projectiveNodeToBase K) := by
  intro hs
  letI : AlgebraicGeometry.Smooth (projectiveNodeToBase K) := hs
  have h : AlgebraicGeometry.Smooth (affineOpen K ≫ projectiveNodeToBase K) := inferInstance
  rw [affineOpen_toBase] at h
  have ha : (algebraMap K (coordinates K)).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mp h
  exact affineNode_not_smooth K (RingHom.smooth_algebraMap.mp ha)

end
end ManuscriptAudit.NodalSmoothCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothCharts.puncturedAffineAlgebra_smooth,
      ``ManuscriptAudit.NodalSmoothCharts.yChartAlgebra_smooth,
      ``ManuscriptAudit.NodalSmoothCharts.projectiveNode_not_smooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
