import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ManuscriptAudit.OddTheta

/-- This is the character specified in Paper 8, p. 361. The residue formula is
`ZMod.χ₄_int_eq_if_mod_four`. -/
def paperChi4 (n : ℤ) : ℂ :=
  (ZMod.χ₄ (n : ZMod 4) : ℂ)

private theorem paperChi4_neg (n : ℤ) : paperChi4 (-n) = -paperChi4 n := by
  have hAtNegOne : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  have hInt : ZMod.χ₄ ((-n : ℤ) : ZMod 4) = -ZMod.χ₄ (n : ZMod 4) := by
    calc
      _ = ZMod.χ₄ ((-1 : ZMod 4) * (n : ZMod 4)) := by simp
      _ = -ZMod.χ₄ (n : ZMod 4) := by rw [map_mul, hAtNegOne, neg_one_mul]
  unfold paperChi4
  rw [hInt, Int.cast_neg]

private theorem paperChi4_norm_le_one (n : ℤ) : ‖paperChi4 n‖ ≤ 1 := by
  rcases ZMod.isQuadratic_χ₄ (n : ZMod 4) with h | h | h <;>
    simp [paperChi4, h]

/-- Paper 8, pp. 360–361, equation (I.1). The bilateral theta series is
absolutely convergent on the upper half-plane and has sum zero. -/
theorem paperTheta_hasSum_zero (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => paperChi4 n *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)) 0 := by
  let term : ℤ → ℂ := fun n => paperChi4 n * jacobiTheta₂_term n 0 τ
  have hGaussian : Summable fun n : ℤ => ‖jacobiTheta₂_term n 0 τ‖ :=
    (summable_norm_iff (E := ℂ)).2 ((summable_jacobiTheta₂_term_iff 0 τ).2 hτ)
  have hSum : Summable term := hGaussian.of_norm_bounded fun n => by
    change ‖paperChi4 n * jacobiTheta₂_term n 0 τ‖ ≤ ‖jacobiTheta₂_term n 0 τ‖
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right
        (paperChi4_norm_le_one n) (norm_nonneg (jacobiTheta₂_term n 0 τ))
  have hOdd (n : ℤ) : term (-n) = -term n := by
    simp only [term, paperChi4_neg, jacobiTheta₂_term, mul_zero, zero_add,
      Int.cast_neg, neg_sq, neg_mul]
  have hZero : term 0 = 0 := by
    simp [term, paperChi4]
  have hPair : (fun n : ℕ => term (n : ℤ) + term (-(n : ℤ))) = (0 : ℕ → ℂ) := by
    funext n
    rw [hOdd]
    exact add_neg_cancel _
  have hPaired := hSum.hasSum.nat_add_neg
  rw [hPair, hZero, add_zero] at hPaired
  have hTotal : (∑' n : ℤ, term n) = 0 := hPaired.unique hasSum_zero
  have h : HasSum term 0 := hTotal ▸ hSum.hasSum
  simpa only [term, jacobiTheta₂_term, mul_zero, zero_add] using h

/-- The height weight in Paper 8, equation (I.1), leaves the kernel zero. -/
theorem paperThetaKernel_eq_zero (τ : ℂ) (hτ : 0 < τ.im) (α : ℝ) :
    (Real.rpow τ.im α : ℂ) * (∑' n : ℤ, paperChi4 n *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)) = 0 := by
  rw [(paperTheta_hasSum_zero τ hτ).tsum_eq, mul_zero]

end ManuscriptAudit.OddTheta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.OddTheta.paperTheta_hasSum_zero,
    ``ManuscriptAudit.OddTheta.paperThetaKernel_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
