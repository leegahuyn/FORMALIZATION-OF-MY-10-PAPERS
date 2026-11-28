import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8CompactCrossDecomposition
import PrimalitySheafVerification.ManuscriptAudit.Paper8CompactEigenvalueIsolation
import PrimalitySheafVerification.ManuscriptAudit.Paper8IsolatedCauchyPole

/-! A nonzero cross pairing for a compact injective self-adjoint resolvent forces a simple pole. -/

namespace ManuscriptAudit.Paper8CompactCrossPole

open Module.End Paper8CompactCrossDecomposition Paper8CompactEigenvalueIsolation Paper8IsolatedCauchyPole
open scoped InnerProductSpace

noncomputable section

theorem compact_injective_cross_resolvent_has_pole {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) (hSymm : T.IsSymmetric)
    (hInjective : Function.Injective T) {x y : H} (hCross : ⟪x, y⟫_ℂ ≠ 0) :
    ∃ μ : Eigenvalues T.toLinearMap,
      MeromorphicAt (cauchySpectralSeries (fun ν : Eigenvalues T.toLinearMap => (ν : ℂ)) (compactCrossCoefficient T hT hSymm x y)) (μ : ℂ) ∧
      meromorphicOrderAt
        (cauchySpectralSeries (fun ν : Eigenvalues T.toLinearMap => (ν : ℂ)) (compactCrossCoefficient T hT hSymm x y)) (μ : ℂ) = (-1 : ℤ) := by
  obtain ⟨μ, hCrossμ⟩ := exists_nonzero_compactCrossCoefficient T hT hSymm hCross
  have hμ : (μ : ℂ) ≠ 0 := by
    intro hZero
    have hE : HasEigenvalue T.toLinearMap (μ : ℂ) := μ.2
    obtain ⟨v, hv, hv₀⟩ := hE.exists_hasEigenvector
    apply hv₀
    apply hInjective
    have hEq := mem_eigenspace_iff.mp hv
    change T v = (μ : ℂ) • v at hEq
    rw [map_zero, hEq, hZero, zero_smul]
  obtain ⟨r, hr, hIso⟩ := compact_eigenvalue_isolated T hT hSymm μ hμ
  exact ⟨μ, cauchySpectralSeries_simple_pole (fun ν : Eigenvalues T.toLinearMap => (ν : ℂ)) _
    (summable_norm_compactCrossCoefficient T hT hSymm x y) μ hCrossμ hr hIso⟩

end
end ManuscriptAudit.Paper8CompactCrossPole

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8CompactCrossPole.compact_injective_cross_resolvent_has_pole
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
