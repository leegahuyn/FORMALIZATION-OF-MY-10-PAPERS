import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusModTwoLinear
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedRecurrence

/-!
# The mod-two traces of Frobenius powers

Cayley–Hamilton yields the degree-two recurrence on the genuine
two-dimensional representation. When the first trace and determinant
agree with a paper row modulo two, so do all six printed columns.
-/

namespace ManuscriptAudit.FrobeniusModTwoRecurrence

open FrobeniusModTwoLinear Paper5PrintedRecurrence Polynomial

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private abbrev M₂ := Matrix (Fin 2) (Fin 2) (ZMod 2)

private theorem matrix_square (M : M₂) :
    M ^ 2 = M.trace • M - M.det • (1 : M₂) := by
  have h := Matrix.aeval_self_charpoly M
  simp only [Matrix.charpoly_fin_two, map_add, map_sub, map_pow, map_mul, aeval_C,
    aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  calc
    M ^ 2 = (M ^ 2 - M.trace • M + M.det • 1) + (M.trace • M - M.det • 1) := by abel
    _ = _ := by rw [h, zero_add]

theorem matrix_trace_power_recurrence (M : M₂) (n : ℕ) :
    (M ^ (n + 2)).trace =
      M.trace * (M ^ (n + 1)).trace - M.det * (M ^ n).trace := by
  calc
    (M ^ (n + 2)).trace = (M ^ 2 * M ^ n).trace := by rw [Nat.add_comm n 2, pow_add]
    _ = (M.trace • (M ^ (n + 1)) - M.det • (M ^ n)).trace := by
      rw [matrix_square M, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, pow_succ']
    _ = _ := by rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

variable (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
variable (b : Module.Basis (Fin 2) (ZMod 2) V)
variable (F : V ≃ₗ[ZMod 2] V)

private abbrev T (n : ℕ) : ZMod 2 :=
  LinearMap.trace (ZMod 2) V (F.toLinearMap ^ n)

include b

theorem linear_trace_power_recurrence (n : ℕ) :
    T V F (n + 2) =
      LinearMap.trace (ZMod 2) V F.toLinearMap * T V F (n + 1) -
        LinearMap.det F.toLinearMap * T V F n := by
  let M := LinearMap.toMatrix b b F.toLinearMap
  simpa only [M, LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace (ZMod 2) b,
    LinearMap.det_toMatrix] using matrix_trace_power_recurrence M n

theorem linear_characteristic_polynomial [Module.Finite (ZMod 2) V] :
    F.toLinearMap.charpoly = X ^ 2 - C (LinearMap.trace (ZMod 2) V F.toLinearMap) * X + 1 := by
  rw [← LinearMap.charpoly_toMatrix F.toLinearMap b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 2) b, LinearMap.det_toMatrix b, det_eq_one, map_one]

/-- All powers agree after reducing the signed recurrence modulo two. -/
theorem trace_pow_eq_recurrence_mod_two (p : ℕ) (a : ℤ)
    (ha : LinearMap.trace (ZMod 2) V F.toLinearMap = (a : ZMod 2))
    (hp : LinearMap.det F.toLinearMap = (p : ZMod 2)) (n : ℕ) :
    T V F n = (recurrence p a n : ZMod 2) := by
  have hpair : ∀ n : ℕ, T V F n = (recurrence p a n : ZMod 2) ∧
      T V F (n + 1) = (recurrence p a (n + 1) : ZMod 2) := by
    intro n
    induction n with
    | zero =>
      constructor
      · change LinearMap.trace (ZMod 2) V (F.toLinearMap ^ (0 : ℕ)) = (2 : ZMod 2)
        rw [pow_zero, LinearMap.trace_eq_matrix_trace (ZMod 2) b, LinearMap.toMatrix_one,
          Matrix.trace_one, Fintype.card_fin]
      · simpa only [T, pow_one, recurrence] using ha
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      change T V F (n + 2) = (recurrence p a (n + 2) : ZMod 2)
      rw [linear_trace_power_recurrence V b F, ha, hp, ih.1, ih.2]
      simp only [recurrence, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  exact (hpair n).1

theorem printed_columns_mod_two {r : Row} (hr : r ∈ printedRows)
    (ha : LinearMap.trace (ZMod 2) V F.toLinearMap = (r.a1 : ZMod 2))
    (hp : LinearMap.det F.toLinearMap = (r.prime : ZMod 2)) :
    ((List.range 6).map fun i => T V F (i + 1)) =
      r.traceColumns.map (fun a : ℤ => (a : ZMod 2)) := by
  rw [printedRows_recurrence hr, Row.recurrenceColumns, List.map_map]
  congr 1
  funext i
  exact trace_pow_eq_recurrence_mod_two V b F r.prime r.a1 ha hp (i + 1)

end

end ManuscriptAudit.FrobeniusModTwoRecurrence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.FrobeniusModTwoRecurrence.matrix_trace_power_recurrence,
      ``ManuscriptAudit.FrobeniusModTwoRecurrence.linear_trace_power_recurrence,
      ``ManuscriptAudit.FrobeniusModTwoRecurrence.linear_characteristic_polynomial,
      ``ManuscriptAudit.FrobeniusModTwoRecurrence.printed_columns_mod_two] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
