import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedAllTateDeterminants
import PrimalitySheafVerification.ManuscriptAudit.Paper5GeometricFrobeniusInverse
import PrimalitySheafVerification.ManuscriptAudit.RankTwoInverseTrace

/-! The inverse point-Frobenius convention in all 28 printed rows and both rational Tate modules. -/

namespace ManuscriptAudit.Paper5AllPrintedInverseTate

open Module PowerTateModule Paper5PrintedRecurrence Paper5PrintedNonsplitTateTraces
open Paper5PrintedAllTateDeterminants Paper5GeometricFrobeniusInverse RankTwoInverseTrace
open scoped TensorProduct

noncomputable section

variable {r : Row} [Fact r.prime.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

abbrev RationalRowTate := ℚ_[l] ⊗[ℤ_[l]] Tate l (Points (r := r) L)

private def rationalBasis (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) :
    Basis (Fin 2) ℚ_[l] (RationalRowTate (r := r) L l) :=
  Algebra.TensorProduct.basis ℚ_[l] (rowBasis hr L l hl)

def rationalArithmetic : Module.End ℚ_[l] (RationalRowTate (r := r) L l) :=
  (actual (r := r) L l).baseChange ℚ_[l]

theorem rational_coefficients (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℚ_[l] (RationalRowTate (r := r) L l) (rationalArithmetic (r := r) L l) =
        (r.a1 : ℚ_[l]) ∧
      LinearMap.det (rationalArithmetic (r := r) L l) = (r.prime : ℚ_[l]) := by
  let b := rowBasis hr L l hl
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  obtain ⟨ht, hd⟩ := checked_coefficients hr L l hl
  constructor
  · rw [rationalArithmetic, LinearMap.trace_baseChange, ht, map_intCast]
  · rw [rationalArithmetic, determinant_baseChange b, hd, map_natCast]

def arithmeticEquiv (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) :
    RationalRowTate (r := r) L l ≃ₗ[ℚ_[l]] RationalRowTate (r := r) L l := by
  letI := Module.Finite.of_basis (rationalBasis L l hr hl)
  apply LinearMap.equivOfDetNeZero (rationalArithmetic (r := r) L l)
  rw [(rational_coefficients L l hr hl).2]
  exact_mod_cast (printedRows_prime hr).ne_zero

def inverseAction (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) :
    Module.End ℚ_[l] (RationalRowTate (r := r) L l) :=
  (arithmeticEquiv L l hr hl).symm.toLinearMap

theorem inverse_coefficients (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℚ_[l] (RationalRowTate (r := r) L l) (inverseAction L l hr hl) =
        (r.a1 : ℚ_[l]) / (r.prime : ℚ_[l]) ∧
      LinearMap.det (inverseAction L l hr hl) = (r.prime : ℚ_[l])⁻¹ := by
  have hF : (arithmeticEquiv L l hr hl).toLinearMap = rationalArithmetic (r := r) L l := rfl
  obtain ⟨ht, hd⟩ := rational_coefficients L l hr hl
  constructor
  · have hp : (r.prime : ℚ_[l]) ≠ 0 := by exact_mod_cast (printedRows_prime hr).ne_zero
    apply (eq_div_iff hp).mpr
    have h := determinant_mul_trace_inverse (rationalBasis L l hr hl) (arithmeticEquiv L l hr hl)
    rw [hF, ht, hd] at h
    exact (mul_comm _ _).trans h
  · rw [inverseAction, LinearEquiv.det_coe_symm, hF, hd]

theorem inverse_power_det (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) (m : ℕ) :
    LinearMap.det (inverseAction L l hr hl ^ m) = ((r.prime^m : ℕ) : ℚ_[l])⁻¹ := by
  rw [map_pow, (inverse_coefficients L l hr hl).2, ← inv_pow, Nat.cast_pow]

theorem inverse_det_disagrees_with_printed_prime
    (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) :
    LinearMap.det (inverseAction L l hr hl) ≠ (r.prime : ℚ_[l]) := by
  rw [(inverse_coefficients L l hr hl).2]
  intro h
  have hp : (r.prime : ℚ_[l]) ≠ 0 := by exact_mod_cast (printedRows_prime hr).ne_zero
  have h1 := inv_mul_cancel₀ hp
  rw [h, ← pow_two] at h1
  have hNat : r.prime^2 = 1 := by exact_mod_cast h1
  have h5 := printedRows_prime_at_least_five hr
  nlinarith

end
end ManuscriptAudit.Paper5AllPrintedInverseTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5AllPrintedInverseTate.rational_coefficients,
      ``ManuscriptAudit.Paper5AllPrintedInverseTate.inverse_coefficients,
      ``ManuscriptAudit.Paper5AllPrintedInverseTate.inverse_power_det,
      ``ManuscriptAudit.Paper5AllPrintedInverseTate.inverse_det_disagrees_with_printed_prime] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
