import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5GeometricFrobeniusInverse
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenOneTate
import PrimalitySheafVerification.ManuscriptAudit.RankTwoInverseTrace

/-! A nonzero trace distinguishes the two generators on the literal rational Tate module at seven. -/

namespace ManuscriptAudit.Paper5SevenInverseTrace

open Module Paper5OrdinarySevenOneTate PowerTateModule RankTwoInverseTrace
open scoped TensorProduct

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]

abbrev V := ℚ_[2] ⊗[ℤ_[2]] Tate 2 (Geometric L)

private def integralBasis : Basis (Fin 2) ℤ_[2] (Tate 2 (Geometric L)) :=
  tateBasis L 2 (Or.inl rfl)

private def rationalBasis : Basis (Fin 2) ℚ_[2] (V L) :=
  Algebra.TensorProduct.basis ℚ_[2] (integralBasis L)

def arithmetic : Module.End ℚ_[2] (V L) :=
  (action L 2).baseChange ℚ_[2]

theorem arithmetic_coefficients :
    LinearMap.trace ℚ_[2] (V L) (arithmetic L) = -4 ∧
      LinearMap.det (arithmetic L) = 7 := by
  letI := Module.Free.of_basis (integralBasis L)
  letI := Module.Finite.of_basis (integralBasis L)
  obtain ⟨hT, hD⟩ := trace_det L 2 (Or.inl rfl)
  constructor
  · rw [arithmetic, LinearMap.trace_baseChange, hT]
    norm_num
  · rw [arithmetic, Paper5GeometricFrobeniusInverse.determinant_baseChange (integralBasis L), hD]
    norm_num

def arithmeticEquiv : V L ≃ₗ[ℚ_[2]] V L := by
  letI : Module.Finite ℚ_[2] (V L) := Module.Finite.of_basis (rationalBasis L)
  apply LinearMap.equivOfDetNeZero (arithmetic L)
  rw [(arithmetic_coefficients L).2]
  norm_num

def inverseGenerator : Module.End ℚ_[2] (V L) :=
  (arithmeticEquiv L).symm.toLinearMap

theorem inverse_coefficients :
    LinearMap.trace ℚ_[2] (V L) (inverseGenerator L) = (-4 : ℚ_[2])/7 ∧
      LinearMap.det (inverseGenerator L) = (7 : ℚ_[2])⁻¹ := by
  have hF : (arithmeticEquiv L).toLinearMap = arithmetic L := rfl
  obtain ⟨ht, hd⟩ := arithmetic_coefficients L
  constructor
  · apply (eq_div_iff (by norm_num : (7 : ℚ_[2]) ≠ 0)).mpr
    have h := determinant_mul_trace_inverse (rationalBasis L) (arithmeticEquiv L)
    rw [hF, ht, hd] at h
    exact (mul_comm _ _).trans h
  · rw [inverseGenerator, LinearEquiv.det_coe_symm, hF, hd]

end
end ManuscriptAudit.Paper5SevenInverseTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5SevenInverseTrace.arithmetic_coefficients,
      ``ManuscriptAudit.Paper5SevenInverseTrace.inverse_coefficients] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
