import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import PrimalitySheafVerification.ManuscriptAudit.LocalTraceExponential

/-! A native local trace-determinant formula, including non-diagonal upper triangular matrices. -/

namespace ManuscriptAudit.LocalTriangularTraceDeterminant

open Matrix LocalTraceExponential
open scoped BigOperators

noncomputable section

variable {ι : Type} [Fintype ι] [LinearOrder ι]

def traceTerm (M : Matrix ι ι ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  z ^ (n + 1) * (M ^ (n + 1)).trace / ((n + 1 : ℕ) : ℂ)

private theorem triangular_mul_diag {M N : Matrix ι ι ℂ}
    (hM : M.BlockTriangular id) (hN : N.BlockTriangular id) (i : ι) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hM hj, zero_mul]
    · rw [hN hj, mul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

private theorem triangular_power_diag {M : Matrix ι ι ℂ} (hM : M.BlockTriangular id)
    (n : ℕ) (i : ι) : (M ^ n) i i = (M i i) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, triangular_mul_diag (hM.pow n) hM, ih, pow_succ]

theorem trace_power_eq_sum {M : Matrix ι ι ℂ} (hM : M.BlockTriangular id) (n : ℕ) :
    (M ^ n).trace = ∑ i : ι, (M i i) ^ n := by
  simp only [Matrix.trace, Matrix.diag_apply, triangular_power_diag hM]

private theorem traceTerm_eq_sum {M : Matrix ι ι ℂ} (hM : M.BlockTriangular id) (z : ℂ) (n : ℕ) :
    traceTerm M z n = ∑ i : ι, term n (z * M i i) := by
  simp only [traceTerm, trace_power_eq_sum hM, term, mul_pow, div_eq_mul_inv, Finset.mul_sum,
    Finset.sum_mul]

private theorem finite_tsum (I : Finset ι) (f : ι → ℕ → ℂ)
    (hf : ∀ i ∈ I, Summable (f i)) :
    Summable (fun n => ∑ i ∈ I, f i n) ∧
      (∑' n : ℕ, ∑ i ∈ I, f i n) = ∑ i ∈ I, ∑' n : ℕ, f i n := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    have hfi := hf i (Finset.mem_insert_self i I)
    obtain ⟨hRest, he⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    exact ⟨hfi.add hRest, (hfi.tsum_add hRest).trans (congrArg (fun x => (∑' n, f i n) + x) he)⟩

private theorem exp_finite_sum (I : Finset ι) (f : ι → ℂ) :
    Complex.exp (∑ i ∈ I, f i) = ∏ i ∈ I, Complex.exp (f i) := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Complex.exp_add, ih]

private theorem determinant_eq (M : Matrix ι ι ℂ) (hM : M.BlockTriangular id) (z : ℂ) :
    ((1 : Matrix ι ι ℂ) - z • M).det = ∏ i : ι, (1 - z * M i i) := by
  have hZ : (z • M).BlockTriangular id := by
    intro i j h
    simp [Matrix.smul_apply, hM h]
  have hTri : ((1 : Matrix ι ι ℂ) - z • M).BlockTriangular id :=
    Matrix.blockTriangular_one.sub hZ
  rw [Matrix.det_of_upperTriangular hTri]
  apply Finset.prod_congr rfl
  intro i _
  simp [Matrix.sub_apply, Matrix.smul_apply]

theorem trace_series_summable {M : Matrix ι ι ℂ} (hM : M.BlockTriangular id) (z : ℂ)
    (hz : ∀ i : ι, ‖z * M i i‖ < 1) : Summable (traceTerm M z) := by
  have hs (i : ι) : Summable (fun n => term n (z * M i i)) :=
    (term_norm_summable (hz i)).of_norm
  rw [show traceTerm M z = (fun n => ∑ i : ι, term n (z * M i i)) from
    funext (traceTerm_eq_sum hM z)]
  exact (finite_tsum Finset.univ _ (fun i _ => hs i)).1

/-- The actual determinant of 1−zM is the inverse exponential of the
convergent trace-of-powers series at every strictly allowed z. -/
theorem exp_trace_series_eq_inverse_det {M : Matrix ι ι ℂ} (hM : M.BlockTriangular id) (z : ℂ)
    (hz : ∀ i : ι, ‖z * M i i‖ < 1) :
    Complex.exp (∑' n : ℕ, traceTerm M z n) = (((1 : Matrix ι ι ℂ) - z • M).det)⁻¹ := by
  have hs (i : ι) : Summable (fun n => term n (z * M i i)) :=
    (term_norm_summable (hz i)).of_norm
  have hSum := (finite_tsum Finset.univ _ (fun i _ => hs i)).2
  rw [show traceTerm M z = (fun n => ∑ i : ι, term n (z * M i i)) from
    funext (traceTerm_eq_sum hM z), hSum]
  change Complex.exp (∑ i : ι, traceLog (z * M i i)) = _
  rw [exp_finite_sum, determinant_eq M hM z]
  have hExp (i : ι) : Complex.exp (traceLog (z * M i i)) = (1 - z * M i i)⁻¹ :=
    exp_traceLog (hz i)
  simp only [hExp, Finset.prod_inv_distrib]

end
end ManuscriptAudit.LocalTriangularTraceDeterminant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.LocalTriangularTraceDeterminant.trace_power_eq_sum,
      ``ManuscriptAudit.LocalTriangularTraceDeterminant.trace_series_summable,
      ``ManuscriptAudit.LocalTriangularTraceDeterminant.exp_trace_series_eq_inverse_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
