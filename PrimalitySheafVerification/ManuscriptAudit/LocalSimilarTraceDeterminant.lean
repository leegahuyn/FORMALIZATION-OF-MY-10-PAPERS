import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.LocalTriangularTraceDeterminant

/-! Trace series and local determinants are invariant under an actual change of basis. -/

namespace ManuscriptAudit.LocalSimilarTraceDeterminant

open Matrix LocalTriangularTraceDeterminant

noncomputable section

variable {ι : Type} [Fintype ι] [LinearOrder ι]

private abbrev M := Matrix ι ι ℂ

def conjugate (P : (M (ι := ι))ˣ) (A : M (ι := ι)) : M (ι := ι) :=
  P.val * A * (P⁻¹).val

private theorem conjugate_pow (P : (M (ι := ι))ˣ) (A : M (ι := ι)) (n : ℕ) :
    conjugate P (A ^ n) = conjugate P A ^ n := by
  induction n with
  | zero => simp [conjugate]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    have hP : (P⁻¹).val * P.val = 1 := by simp
    change P.val * (A ^ n * A) * (P⁻¹).val =
      (P.val * A ^ n * (P⁻¹).val) * (P.val * A * (P⁻¹).val)
    calc
      _ = (P.val * A ^ n * ((P⁻¹).val * P.val)) * A * (P⁻¹).val := by
        rw [hP, mul_one, mul_assoc P.val (A ^ n) A]
      _ = _ := by simp only [mul_assoc]

theorem trace_conjugate_power (P : (M (ι := ι))ˣ) (A : M (ι := ι)) (n : ℕ) :
    (conjugate P A ^ n).trace = (A ^ n).trace := by
  rw [← conjugate_pow]
  exact Matrix.trace_units_conj P (A ^ n)

private theorem det_conjugate (P : (M (ι := ι))ˣ) (A : M (ι := ι)) :
    (conjugate P A).det = A.det := by
  rw [conjugate, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = A.det * (P.val.det * (P⁻¹).val.det) := by ring
    _ = _ := by rw [← Matrix.det_mul]; simp

theorem determinant_one_sub_conjugate (P : (M (ι := ι))ˣ) (A : M (ι := ι)) (z : ℂ) :
    ((1 : M) - z • conjugate P A).det = ((1 : M) - z • A).det := by
  have h : (1 : M) - z • conjugate P A = conjugate P ((1 : M) - z • A) := by
    unfold conjugate
    rw [mul_sub, sub_mul, mul_one]
    have hP : P.val * (P⁻¹).val = 1 := by simp
    rw [hP]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [h, det_conjugate]

theorem native_trace_series_of_triangular_conjugate (P : (M (ι := ι))ˣ) (A : M (ι := ι))
    (hA : A.BlockTriangular id) (z : ℂ) (hz : ∀ i, ‖z * A i i‖ < 1) :
    Summable (traceTerm (conjugate P A) z) ∧
      Complex.exp (∑' n : ℕ, traceTerm (conjugate P A) z n) =
        (((1 : M) - z • conjugate P A).det)⁻¹ := by
  have hTerm : traceTerm (conjugate P A) z = traceTerm A z := by
    funext n
    rw [traceTerm, traceTerm, trace_conjugate_power]
  rw [hTerm, determinant_one_sub_conjugate]
  exact ⟨trace_series_summable hA z hz, exp_trace_series_eq_inverse_det hA z hz⟩

end
end ManuscriptAudit.LocalSimilarTraceDeterminant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.LocalSimilarTraceDeterminant.trace_conjugate_power,
      ``ManuscriptAudit.LocalSimilarTraceDeterminant.determinant_one_sub_conjugate,
      ``ManuscriptAudit.LocalSimilarTraceDeterminant.native_trace_series_of_triangular_conjugate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
