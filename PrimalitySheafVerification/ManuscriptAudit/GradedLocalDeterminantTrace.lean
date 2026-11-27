import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.Parity
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import PrimalitySheafVerification.ManuscriptAudit.LocalDeterminantTraceExpansion

/-! A finite graded local factor is the exponential of its convergent supertrace series. -/

namespace ManuscriptAudit.GradedLocalDeterminantTrace

open LocalDeterminantTraceExpansion
open scoped BigOperators

noncomputable section

variable {V : ℕ → Type}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]

def supertrace (I : Finset ℕ) (F : ∀ i, Module.End ℂ (V i)) (n : ℕ) : ℂ :=
  ∑ i ∈ I, (-1 : ℂ) ^ i * LinearMap.trace ℂ (V i) (F i ^ n)

def gradedTerm (I : Finset ℕ) (F : ∀ i, Module.End ℂ (V i)) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ I, (-1 : ℂ) ^ i * term (F i) z n

def localPiece (F : ∀ i, Module.End ℂ (V i)) (z : ℂ) (i : ℕ) : ℂ :=
  if Even i then (LinearMap.det ((1 : Module.End ℂ (V i)) - z • F i))⁻¹
  else LinearMap.det ((1 : Module.End ℂ (V i)) - z • F i)

def localFactor (I : Finset ℕ) (F : ∀ i, Module.End ℂ (V i)) (z : ℂ) : ℂ :=
  ∏ i ∈ I, localPiece F z i

theorem term_eq_supertrace (I : Finset ℕ) (F : ∀ i, Module.End ℂ (V i)) (z : ℂ) (n : ℕ) :
    gradedTerm I F z n = z ^ (n + 1) * supertrace I F (n + 1) / ((n + 1 : ℕ) : ℂ) := by
  simp only [gradedTerm, supertrace, term, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem signed_piece (F : ∀ i, Module.End ℂ (V i)) (z : ℂ) (i : ℕ)
    (h : ∀ a : ℂ, (F i).HasEigenvalue a → ‖z * a‖ < 1) :
    Summable (fun n => (-1 : ℂ) ^ i * term (F i) z n) ∧
      Complex.exp (∑' n : ℕ, (-1 : ℂ) ^ i * term (F i) z n) = localPiece F z i := by
  obtain ⟨hS, hExp⟩ := native_det_trace_expansion (F i) z h
  refine ⟨hS.mul_left ((-1 : ℂ) ^ i), ?_⟩
  rw [hS.tsum_mul_left]
  by_cases hEven : Even i
  · simpa only [localPiece, if_pos hEven, hEven.neg_one_pow, one_mul] using hExp
  · have hOdd : (-1 : ℂ) ^ i = -1 := by rw [neg_one_pow_eq_ite, if_neg hEven]
    rw [hOdd, neg_one_mul, Complex.exp_neg, hExp, inv_inv, localPiece, if_neg hEven]

theorem exp_supertrace_eq_local_factor (I : Finset ℕ) (F : ∀ i, Module.End ℂ (V i)) (z : ℂ)
    (h : ∀ i ∈ I, ∀ a : ℂ, (F i).HasEigenvalue a → ‖z * a‖ < 1) :
    Summable (gradedTerm I F z) ∧
      Complex.exp (∑' n : ℕ, gradedTerm I F z n) = localFactor I F z := by
  induction I using Finset.induction_on with
  | empty =>
    have hzero : gradedTerm (∅ : Finset ℕ) F z = (fun _ => (0 : ℂ)) := by
      funext n
      simp [gradedTerm]
    simp [hzero, localFactor]
  | insert i I hI ih =>
    obtain ⟨hOne, heOne⟩ := signed_piece F z i (h i (Finset.mem_insert_self i I))
    obtain ⟨hRest, heRest⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have he : gradedTerm (insert i I) F z =
        fun n => (-1 : ℂ) ^ i * term (F i) z n + gradedTerm I F z n := by
      funext n
      rw [gradedTerm, Finset.sum_insert hI, gradedTerm]
    rw [he]
    refine ⟨hOne.add hRest, ?_⟩
    rw [hOne.tsum_add hRest, Complex.exp_add, heOne, heRest]
    simp only [localFactor, Finset.prod_insert hI]

end
end ManuscriptAudit.GradedLocalDeterminantTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GradedLocalDeterminantTrace.term_eq_supertrace,
      ``ManuscriptAudit.GradedLocalDeterminantTrace.exp_supertrace_eq_local_factor] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
