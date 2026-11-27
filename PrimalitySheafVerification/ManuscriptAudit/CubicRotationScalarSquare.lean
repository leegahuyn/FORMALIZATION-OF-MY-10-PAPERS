import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools

/-! Rank-two trace and determinant for a cubic rotation inverted by a scalar-square map. -/

namespace ManuscriptAudit.CubicRotationScalarSquare

open Polynomial Module

variable {R V : Type*} [CommRing R] [IsDomain R] [CharZero R]
variable [AddCommGroup V] [Module R V]

theorem trace_det (B : Basis (Fin 2) R V) (F S : Module.End R V) {c : R}
    (hc : c ≠ 0) (hF : F ^ 2 = c • (1 : Module.End R V))
    (hS : S ^ 2 + S + 1 = 0) (hConj : F * S = S ^ 2 * F) :
    LinearMap.trace R V S = -1 ∧ LinearMap.det S = 1 := by
  let tr := LinearMap.trace R V
  have hMul : F * S * F = S ^ 2 * (F ^ 2) := by
    rw [hConj, mul_assoc, pow_two F]
  have hWeight : c * tr (S ^ 2) = c * tr S := by
    calc
      _ = tr (S ^ 2 * (F ^ 2)) := by rw [hF, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
      _ = tr (F * S * F) := congrArg tr hMul.symm
      _ = tr ((F ^ 2) * S) := by
        change LinearMap.trace R V (F * S * F) = LinearMap.trace R V ((F ^ 2) * S)
        rw [LinearMap.trace_mul_comm R (F * S) F, ← mul_assoc, ← pow_two]
      _ = _ := by rw [hF, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  have hEqual : tr (S ^ 2) = tr S := mul_left_cancel₀ hc hWeight
  have hFin : finrank R V = 2 := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  have hOne : tr (1 : Module.End R V) = 2 := by
    change LinearMap.trace R V 1 = 2
    rw [LinearMap.trace_one, hFin] <;> rfl
  have hSum : tr S + tr S + 2 = 0 := by
    simpa only [map_add, map_zero, hEqual, hOne] using congrArg tr hS
  have hProd : 2 * (tr S + 1) = 0 := by linear_combination hSum
  have hTrace : tr S = -1 :=
    eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hProd).resolve_left two_ne_zero)
  constructor
  · exact hTrace
  letI : Module.Free R V := Module.Free.of_basis B
  letI : Module.Finite R V := Module.Finite.of_basis B
  have hChar : S.charpoly = X ^ 2 + X + C (LinearMap.det S) := by
    rw [← LinearMap.charpoly_toMatrix S B, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace R B, LinearMap.det_toMatrix B]
    change X ^ 2 - C (tr S) * X + C (LinearMap.det S) = _
    simp [hTrace, sub_eq_add_neg]
  have hCH := LinearMap.aeval_self_charpoly S
  rw [hChar] at hCH
  simp only [map_add, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hCH
  have hEq : LinearMap.det S • (1 : Module.End R V) = 1 :=
    add_left_cancel (hCH.trans hS.symm)
  have he := congrArg (fun T : Module.End R V => (B.repr (T (B 0))) (0 : Fin 2)) hEq
  change (B.repr (LinearMap.det S • B 0)) 0 = (B.repr (B 0)) 0 at he
  simpa only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using he

end ManuscriptAudit.CubicRotationScalarSquare

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationScalarSquare.trace_det
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
