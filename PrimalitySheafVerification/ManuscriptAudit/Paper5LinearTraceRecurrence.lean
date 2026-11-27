import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedRecurrence

/-! The printed recurrence is the actual trace sequence of a rank-two operator with its coefficients. -/

namespace ManuscriptAudit.Paper5LinearTraceRecurrence

open Polynomial Module Paper5PrintedRecurrence

noncomputable section

variable {R V : Type*} [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]

/-- Cayley–Hamilton identifies the six printed columns and every later column on any actual module. -/
theorem trace_pow_eq_recurrence (B : Basis (Fin 2) R V) (F : Module.End R V) (p : ℕ) (a : ℤ)
    (ht : LinearMap.trace R V F = (a : R)) (hd : LinearMap.det F = (p : R)) (n : ℕ) :
    LinearMap.trace R V (F ^ n) = (recurrence p a n : R) := by
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  have hchar : F.charpoly = X ^ 2 - C (a : R) * X + C (p : R) := by
    rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace R B, LinearMap.det_toMatrix B, ht, hd]
  have hCH := LinearMap.aeval_self_charpoly F
  rw [hchar] at hCH
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul] at hCH
  have hSquare : F ^ 2 = (a : R) • F - (p : R) • (1 : Module.End R V) := by
    apply eq_sub_iff_add_eq.mpr
    apply sub_eq_zero.mp
    calc
      _ = F ^ 2 - (a : R) • F + (p : R) • (1 : Module.End R V) := by abel
      _ = 0 := hCH
  have hStep (k : ℕ) : F ^ (k + 2) = (a : R) • F ^ (k + 1) - (p : R) • F ^ k := by
    rw [pow_add, hSquare, mul_sub, Algebra.mul_smul_comm, Algebra.mul_smul_comm,
      mul_one, ← pow_succ]
  have h0 : LinearMap.trace R V (1 : Module.End R V) = (2 : R) := by
    simp [LinearMap.trace_eq_matrix_trace R B]
  induction n using Nat.twoStepInduction with
  | zero => simpa only [pow_zero, recurrence, Int.cast_ofNat] using h0
  | one => simpa only [pow_one, recurrence] using ht
  | more n ih ih' =>
    rw [hStep, map_sub, map_smul, map_smul, ih, ih', recurrence,
      Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast, smul_eq_mul, smul_eq_mul]

end
end ManuscriptAudit.Paper5LinearTraceRecurrence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5LinearTraceRecurrence.trace_pow_eq_recurrence
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
