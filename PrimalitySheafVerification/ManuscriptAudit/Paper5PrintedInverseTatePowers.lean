import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5AllPrintedInverseTate

/-! The native inverse and dual generator coefficients for every power of every printed original row. -/

namespace ManuscriptAudit.Paper5PrintedInverseTatePowers

open Module PowerTateModule Paper5AllPrintedInverseTate Paper5PrintedRecurrence
open Paper5PrintedNonsplitTateTraces Paper5PrintedAllTateDeterminants RankTwoInverseTrace

noncomputable section

private theorem linearMap_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (n : ℕ) :
    (e^n).toLinearMap = e.toLinearMap^n :=
  map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) e n

private theorem inverse_linearMap_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (n : ℕ) :
    (e^n).symm.toLinearMap = e.symm.toLinearMap^n := by
  have h : (e^n).symm = e.symm^n := by
    change (e^n)⁻¹ = (e⁻¹)^n
    rw [inv_pow]
  rw [h, linearMap_pow]

variable {r : Row} [Fact r.prime.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

theorem arithmetic_power_trace (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) (n : ℕ) :
    LinearMap.trace ℚ_[l] (RationalRowTate (r := r) L l)
      (rationalArithmetic (r := r) L l ^ n) =
      (recurrence r.prime r.a1 n : ℚ_[l]) := by
  let b := rowBasis hr L l hl
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  rw [rationalArithmetic, ← LinearMap.baseChange_pow, LinearMap.trace_baseChange,
    all_printed_power_traces hr L l hl n, map_intCast]

theorem inverse_power_trace (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) (n : ℕ) :
    LinearMap.trace ℚ_[l] (RationalRowTate (r := r) L l)
      (inverseAction L l hr hl ^ n) =
      (recurrence r.prime r.a1 n : ℚ_[l]) / ((r.prime^n : ℕ) : ℚ_[l]) := by
  let e := arithmeticEquiv L l hr hl
  let b := Algebra.TensorProduct.basis ℚ_[l] (rowBasis hr L l hl)
  have hE : (e^n).toLinearMap = rationalArithmetic (r := r) L l ^ n := linearMap_pow e n
  have hI : (e^n).symm.toLinearMap = inverseAction L l hr hl ^ n := inverse_linearMap_pow e n
  have hd : LinearMap.det ((e^n).toLinearMap) = ((r.prime^n : ℕ) : ℚ_[l]) := by
    rw [hE, map_pow, (rational_coefficients L l hr hl).2, Nat.cast_pow]
  have ht := arithmetic_power_trace L l hr hl n
  have hp : ((r.prime^n : ℕ) : ℚ_[l]) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero n (by exact_mod_cast (printedRows_prime hr).ne_zero)
  apply (eq_div_iff hp).mpr
  have h := determinant_mul_trace_inverse b (e^n)
  rw [hI, hd, hE, ht] at h
  exact (mul_comm _ _).trans h

theorem dual_inverse_power_trace (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) (n : ℕ) :
    let e := arithmeticEquiv L l hr hl
    LinearMap.trace ℚ_[l] (Module.Dual ℚ_[l] (RationalRowTate (r := r) L l))
      (FrobeniusDualConvention.dualAction (e^n).symm) = (recurrence r.prime r.a1 n : ℚ_[l]) := by
  let e := arithmeticEquiv L l hr hl
  let b := Algebra.TensorProduct.basis ℚ_[l] (rowBasis hr L l hl)
  have h := (FrobeniusDualConvention.inverse_generator_coefficients b (e^n)).1
  have hE : (e^n).toLinearMap = rationalArithmetic (r := r) L l ^ n := linearMap_pow e n
  rw [hE] at h
  exact h.trans (arithmetic_power_trace L l hr hl n)

end
end ManuscriptAudit.Paper5PrintedInverseTatePowers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedInverseTatePowers.arithmetic_power_trace,
      ``ManuscriptAudit.Paper5PrintedInverseTatePowers.inverse_power_trace,
      ``ManuscriptAudit.Paper5PrintedInverseTatePowers.dual_inverse_power_trace] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
