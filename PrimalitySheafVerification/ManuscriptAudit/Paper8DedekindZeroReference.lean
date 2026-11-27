import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8AllResidueDivisorSum

/-!
# The sign of the reference's zero-frequency Dedekind sum

Ahlgren and Andersen (1.2), https://arxiv.org/pdf/1504.02500 ,
use exp(π i s(d,D)) at frequency zero. Taking d in [0,D)
instead of (0,D] leaves the coprime residue sum unchanged.
-/

namespace ManuscriptAudit.Paper8DedekindZeroReference

open Paper8ContourResidueWeights (sawtooth dedekindSum)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8GcdArithmeticWeight (frequencyWeight)
open Paper8AllResidueDivisorSum (reducedFrequencySum)

noncomputable section

private theorem sawtooth_neg (x : ℚ) : sawtooth (-x) = -sawtooth x := by
  by_cases hx : x = (⌊x⌋ : ℚ)
  · obtain ⟨z, rfl⟩ : ∃ z : ℤ, (z : ℚ) = x := ⟨⌊x⌋, hx.symm⟩
    simp only [sawtooth, ← Int.cast_neg, Int.floor_intCast, if_pos rfl, neg_zero]
  · have hLower : (⌊x⌋ : ℚ) < x := lt_of_le_of_ne (Int.floor_le x) hx.symm
    have hUpper : x < (⌊x⌋ : ℚ) + 1 := Int.lt_floor_add_one x
    have hFloor : ⌊-x⌋ = -⌊x⌋ - 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    have hNeg : -x ≠ (⌊-x⌋ : ℚ) := by
      rw [hFloor]
      push_cast
      linarith
    simp only [sawtooth, if_neg hx, if_neg hNeg, hFloor]
    push_cast
    ring

theorem dedekindSum_neg (d : ℤ) (D : ℕ) : dedekindSum (-d) D = -dedekindSum d D := by
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.cast_neg, neg_mul, neg_div, sawtooth_neg, mul_neg]

def referenceZeroSum (D : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ.filter (fun d : Fin D => Nat.Coprime d.val D)),
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (d.val : ℤ) D : ℝ) : ℂ))

theorem reducedFrequencySum_zero_eq_conj (D : ℕ) :
    reducedFrequencySum D 0 = (starRingEnd ℂ) (referenceZeroSum D) := by
  unfold reducedFrequencySum referenceZeroSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [frequencyWeight, zero_mul, zero_div, add_zero, dedekindSum_neg, Rat.cast_neg,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  rw [periodCoefficient]
  push_cast
  ring

end
end ManuscriptAudit.Paper8DedekindZeroReference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DedekindZeroReference.dedekindSum_neg,
      ``ManuscriptAudit.Paper8DedekindZeroReference.reducedFrequencySum_zero_eq_conj] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
