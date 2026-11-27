import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import PrimalitySheafVerification.ManuscriptAudit.Paper10CriticalBoundaryTrace

/-! A uniform evaluation bound for every Sobolev exponent strictly above one half. -/

namespace ManuscriptAudit.Paper10SupercriticalBoundaryTrace

open Paper10CriticalBoundaryTrace
open scoped BigOperators

noncomputable section

def traceConstant (s : ℝ) : ℝ := ∑' j : ℕ, ((j : ℝ)+1)^(-(2*s))

def FourierEnergy (s : ℝ) {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ j, frequency j ^ (2*s) * (a j)^2

theorem inverse_weights_summable {s : ℝ} (hs : 1 / 2 < s) :
    Summable (fun j : ℕ => ((j : ℝ)+1)^(-(2*s))) := by
  have h0 : Summable (fun j : ℕ => (j : ℝ)^(-(2*s))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h0

theorem uniform_supercritical_trace {s : ℝ} (hs : 1 / 2 < s)
    {n : ℕ} (a : Fin n → ℝ) (x : ℝ) :
    |cosinePolynomial a x|^2 ≤ traceConstant s * FourierEnergy s a := by
  let f (j : Fin n) := (frequency j)^(-(2*s))
  let g (j : Fin n) := (frequency j)^(2*s) * (a j)^2
  let v (j : Fin n) := a j * Real.cos (frequency j*x)
  have hf (j : Fin n) : 0 ≤ f j := by
    exact Real.rpow_nonneg (by unfold frequency; positivity) _
  have hg (j : Fin n) : 0 ≤ g j := by
    exact mul_nonneg (Real.rpow_nonneg (by unfold frequency; positivity) _) (sq_nonneg _)
  have hv (j : Fin n) : v j ^ 2 ≤ f j * g j := by
    have hk : 0 < frequency j := by unfold frequency; positivity
    have hw : f j * (frequency j)^(2*s) = 1 := by
      change (frequency j)^(-(2*s)) * (frequency j)^(2*s) = 1
      rw [← Real.rpow_add hk, neg_add_cancel, Real.rpow_zero]
    have hcos := Real.cos_le_one (frequency j*x)
    have hcos' := Real.neg_one_le_cos (frequency j*x)
    have hProd : 0 ≤ (1 - Real.cos (frequency j*x)) * (1 + Real.cos (frequency j*x)) :=
      mul_nonneg (by linarith) (by linarith)
    have hSquare : (Real.cos (frequency j*x))^2 ≤ 1 := by nlinarith only [hProd]
    change (a j * Real.cos (frequency j*x))^2 ≤ f j * ((frequency j)^(2*s) * (a j)^2)
    rw [mul_pow, ← mul_assoc, hw, one_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSquare (sq_nonneg (a j))
  have hsum : (∑ j : Fin n, f j) ≤ traceConstant s := by
    change (∑ j : Fin n, ((j.val : ℝ)+1)^(-(2*s))) ≤ traceConstant s
    rw [Fin.sum_univ_eq_sum_range]
    exact (inverse_weights_summable hs).sum_le_tsum _
      (fun j _ => Real.rpow_nonneg (by positivity) _)
  calc
    |cosinePolynomial a x|^2 = (∑ j : Fin n, v j)^2 := by rw [sq_abs]; rfl
    _ ≤ (∑ j : Fin n, f j) * (∑ j : Fin n, g j) :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => hf j)
        (fun j _ => hg j) (fun j _ => hv j)
    _ ≤ traceConstant s * FourierEnergy s a :=
      mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg (fun j _ => hg j))

end
end ManuscriptAudit.Paper10SupercriticalBoundaryTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10SupercriticalBoundaryTrace.inverse_weights_summable,
      ``ManuscriptAudit.Paper10SupercriticalBoundaryTrace.uniform_supercritical_trace] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
