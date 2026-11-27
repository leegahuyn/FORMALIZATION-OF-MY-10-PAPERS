import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicPointScaling

/-! Over an algebraically closed field, nonsingular centered cubics are additively equivalent. -/

namespace ManuscriptAudit.CubicGeometricScaling

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicPointScaling

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A B : K}

/-- A sixth root of the ratio gives the geometric point-group equivalence. -/
theorem exists_scaleEquiv (hA₀ : A ≠ 0) (hB₀ : B ≠ 0)
    (hA : (shortCubic (0 : K) A).Δ ≠ 0) (hB : (shortCubic (0 : K) B).Δ ≠ 0) :
    Nonempty ((Curve A).Point ≃+ (Curve B).Point) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (B / A) (by decide : 0 < (6 : ℕ))
  have hu₀ : u ≠ 0 := by
    intro h
    exact (div_ne_zero hB₀ hA₀) (by simpa [h] using hu.symm)
  have hAB : u ^ 6 * A = B := by rw [hu, div_mul_cancel₀ _ hA₀]
  exact ⟨scaleEquiv hu₀ hAB hA hB⟩

end
end ManuscriptAudit.CubicGeometricScaling

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicGeometricScaling.exists_scaleEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
