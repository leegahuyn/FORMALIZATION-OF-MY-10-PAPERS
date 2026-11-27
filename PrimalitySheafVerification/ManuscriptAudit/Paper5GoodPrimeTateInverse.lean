import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5GoodPrimeTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5GeometricFrobeniusInverse
import PrimalitySheafVerification.ManuscriptAudit.RankTwoInverseTrace
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusDualConvention

/-! Actual relative inverse Frobenius and its algebraic dual over the coefficient field. -/

namespace ManuscriptAudit.Paper5GoodPrimeTateInverse

open Module PowerTateModule
open CubicNonsplitThreeAdicTrace (GeometricPoints)
open CubicSplitPrimeTateCoefficients (basis)
open CubicSplitPrimeTateExtensions (relative relative_eq_power)
open Paper5GoodPrimeTate (extensionTrace extension_power_coefficients)
open Paper5GeometricFrobeniusInverse (determinant_baseChange)
open RankTwoInverseTrace FrobeniusDualConvention
open scoped TensorProduct Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (L D : Type*) [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L] [Field D] [Fintype D] [DecidableEq D]
  [Algebra (ZMod p) D] [Algebra D L] [IsScalarTower (ZMod p) D L]
variable (l : ℕ) [Fact l.Prime]

abbrev RationalTate (A : ZMod p) :=
  ℚ_[l] ⊗[ℤ_[l]] Tate l (GeometricPoints (ZMod p) L A)

theorem relative_inverse_dual_coefficients (hp : 5 ≤ p) (hl : l = 2 ∨ l = 3)
    {A : ZMod p} (hA : A ≠ 0) :
    let t : ℚ_[l] := extensionTrace p D A
    let q : ℚ_[l] := Fintype.card D
    ∃ e : RationalTate p L l A ≃ₗ[ℚ_[l]] RationalTate p L l A,
      e.toLinearMap = (relative p L D A l).baseChange ℚ_[l] ∧
      LinearMap.trace ℚ_[l] (RationalTate p L l A) e.symm.toLinearMap = t/q ∧
      LinearMap.det e.symm.toLinearMap = q⁻¹ ∧
      LinearMap.trace ℚ_[l] (Module.Dual ℚ_[l] (RationalTate p L l A)) (dualAction e.symm) = t ∧
      LinearMap.det (dualAction e.symm) = q := by
  let G := relative p L D A l
  let F := G.baseChange ℚ_[l]
  let t : ℚ_[l] := extensionTrace p D A
  let q : ℚ_[l] := Fintype.card D
  let B := basis p L hp hA l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let b := Algebra.TensorProduct.basis ℚ_[l] B
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  have h := extension_power_coefficients p L D hp hA l hl
  dsimp only at h
  have hTG : LinearMap.trace ℤ_[l] _ G = (extensionTrace p D A : ℤ_[l]) := by
    dsimp only [G]
    rw [relative_eq_power]
    exact h.1
  have hDG : LinearMap.det G = (Fintype.card D : ℤ_[l]) := by
    dsimp only [G]
    rw [relative_eq_power]
    exact h.2
  have ht : LinearMap.trace ℚ_[l] (RationalTate p L l A) F = t := by
    dsimp only [F, t]
    rw [LinearMap.trace_baseChange, hTG, map_intCast]
  have hd : LinearMap.det F = q := by
    dsimp only [F, q]
    rw [determinant_baseChange B, hDG, map_natCast]
  have hq : q ≠ 0 := by
    change (Fintype.card D : ℚ_[l]) ≠ 0
    exact_mod_cast (show Fintype.card D ≠ 0 from Fintype.card_pos.ne')
  let e := LinearMap.equivOfDetNeZero F (hd.symm ▸ hq)
  have he : e.toLinearMap = F := rfl
  have hDual := inverse_generator_coefficients b e
  rw [he, ht, hd] at hDual
  refine ⟨e, he, ?_, ?_, hDual.1, hDual.2⟩
  · apply (eq_div_iff hq).mpr
    have hi := determinant_mul_trace_inverse b e
    rw [he, ht, hd] at hi
    exact (mul_comm _ _).trans hi
  · rw [LinearEquiv.det_coe_symm, he, hd]

end
end ManuscriptAudit.Paper5GoodPrimeTateInverse

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5GoodPrimeTateInverse.relative_inverse_dual_coefficients
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
