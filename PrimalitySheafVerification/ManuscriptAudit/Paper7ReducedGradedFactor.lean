import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.RatFunc.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper7NoWeightCancellation

/-! Reduction of the graded rational factor preserves polynomial factors up to units. -/

namespace ManuscriptAudit.Paper7ReducedGradedFactor

open Matrix Polynomial Paper7NoWeightCancellation
open scoped BigOperators

noncomputable section

def ratio (P Q : ℂ[X]) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q

theorem reduced_ratio_associated (P Q : ℂ[X]) (hC : IsCoprime P Q) (hQ : Q ≠ 0) :
    Associated (ratio P Q).num P ∧ Associated (ratio P Q).denom Q := by
  have hCross : (ratio P Q).num * Q = P * (ratio P Q).denom :=
    (RatFunc.num_mul_eq_mul_denom_iff (x := ratio P Q) (p := P) hQ).mpr rfl
  have hPN : P ∣ (ratio P Q).num :=
    hC.dvd_of_dvd_mul_right ⟨(ratio P Q).denom, hCross⟩
  have hQD : Q ∣ (ratio P Q).denom :=
    hC.symm.dvd_of_dvd_mul_left ⟨(ratio P Q).num, hCross.symm.trans (mul_comm _ _)⟩
  exact ⟨associated_of_dvd_dvd (RatFunc.num_div_dvd P hQ) hPN,
    associated_of_dvd_dvd (RatFunc.denom_div_dvd P Q) hQD⟩

variable {ι : ℕ → Type} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]

private theorem charpolyRev_ne_zero {i : ℕ} (M : Matrix (ι i) (ι i) ℂ) : M.charpolyRev ≠ 0 := by
  intro h
  have hr : M.charpolyRev.IsRoot 0 := by simp [h, Polynomial.IsRoot]
  exact ((Paper07.charpolyRev_isRoot_iff M 0).mp hr).1 rfl

theorem graded_reduced_factors (I : Finset ℕ) (F : ∀ i, Matrix (ι i) (ι i) ℂ)
    {q : ℝ} (hq : 1 < q) (w : ℕ → ℝ) (hW : Set.InjOn w (↑I : Set ℕ))
    (hPure : ∀ i ∈ I, ∀ α : ℂ, (F i).charpoly.IsRoot α → ‖α‖ = q ^ (w i / 2)) :
    Associated (ratio (oddProduct I F) (evenProduct I F)).num (oddProduct I F) ∧
      Associated (ratio (oddProduct I F) (evenProduct I F)).denom (evenProduct I F) := by
  have hQ : evenProduct I F ≠ 0 := by
    unfold evenProduct
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => charpolyRev_ne_zero (F i))
  exact reduced_ratio_associated _ _ (parity_products_coprime I F hq w hW hPure).symm hQ

end
end ManuscriptAudit.Paper7ReducedGradedFactor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7ReducedGradedFactor.reduced_ratio_associated,
      ``ManuscriptAudit.Paper7ReducedGradedFactor.graded_reduced_factors] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
