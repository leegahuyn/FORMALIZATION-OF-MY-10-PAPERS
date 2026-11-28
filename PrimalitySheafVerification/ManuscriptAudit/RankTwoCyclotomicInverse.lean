import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RankTwoInverseTrace

/-! In rank two, the determinant-scaled inverse has the original trace
and determinant. This is the algebra in the cyclotomic untwisting. -/

namespace ManuscriptAudit.RankTwoCyclotomicInverse

open Module RankTwoInverseTrace

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (b : Basis (Fin 2) K V) (e : V ≃ₗ[K] V) (q : K)
variable (hd : LinearMap.det e.toLinearMap = q) (hq : q ≠ 0)

include b hd hq in
/-- The determinant-scaled inverse in dimension two has the original
trace and determinant. -/
theorem trace_det :
    LinearMap.trace K V (q • e.symm.toLinearMap) = LinearMap.trace K V e.toLinearMap ∧
      LinearMap.det (q • e.symm.toLinearMap) = q := by
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  have hrank : finrank K V = 2 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  constructor
  · rw [map_smul, smul_eq_mul, ← hd]
    exact determinant_mul_trace_inverse b e
  · rw [LinearMap.det_smul, hrank, LinearEquiv.det_coe_symm, hd, pow_two,
      mul_assoc, mul_inv_cancel₀ hq, mul_one]

end

end ManuscriptAudit.RankTwoCyclotomicInverse

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RankTwoCyclotomicInverse.trace_det
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
