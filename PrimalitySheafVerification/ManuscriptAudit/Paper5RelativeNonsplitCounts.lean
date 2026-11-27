import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicEvenExtensionPointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitExtensionRecurrence

/-! Signed point counts over arbitrary relative extensions of a nonsplit finite field. -/

namespace ManuscriptAudit.Paper5RelativeNonsplitCounts

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicEvenExtensionPointCounts CubicOddExtensionTrace
open Paper5PrintedRecurrence Paper5NonsplitExtensionRecurrence
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve paper5_traceCurve_trace_eq_zero)

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (F E : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] [CharP F p]
variable [Field E] [Fintype E] [DecidableEq E] [Algebra F E] [Algebra (ZMod p) E]
variable [CharP E p] [IsScalarTower (ZMod p) F E]

private theorem odd_finrank (hP : p % 3 = 2) (hQ : Fintype.card F % 3 = 2) :
    Odd (Module.finrank (ZMod p) F) := by
  let d := Module.finrank (ZMod p) F
  have hCard : Fintype.card F = p ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := F), ZMod.card]
  rcases Nat.even_or_odd d with hd | hd
  · obtain ⟨t, ht⟩ := hd
    have hEven : d = 2 * t := by omega
    have hSq : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hP]; decide
    have e : p ^ d % 3 = 1 := by
      rw [hEven, pow_mul, Nat.pow_mod, hSq, one_pow]
    rw [hCard, e] at hQ
    omega
  · exact hd

private theorem prime_base_unit_curve :
    (paper5TraceCurve p (1 : ZMod p)).baseChange E = shortCubic (0 : E) 1 := by
  ext <;> simp [paper5TraceCurve, shortCubic, WeierstrassCurve.baseChange]

theorem signed_counts (hp : 5 ≤ p) (hP : p % 3 = 2) (hQ : Fintype.card F % 3 = 2)
    {a : F} (ha : a ≠ 0) :
    (Fintype.card E : ℤ) + 1 -
        (Nat.card (shortCubic (0 : E) (algebraMap F E a)).toProjective.Point : ℤ) =
      recurrence (Fintype.card F) 0 (Module.finrank F E) := by
  let d := Module.finrank (ZMod p) F
  let n := Module.finrank F E
  have hDegree : Module.finrank (ZMod p) E = d * n :=
    (Module.finrank_mul_finrank (ZMod p) F E).symm
  have hCard : Fintype.card F = p ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := F), ZMod.card]
  have hOdd : Odd d := odd_finrank p F hP hQ
  have hF₂ : ringChar F ≠ 2 := by rw [ringChar.eq F p]; omega
  have hE₂ : ringChar E ≠ 2 := by rw [ringChar.eq E p]; omega
  have small_ne (b : ℕ) (hb : 0 < b) (hb' : b < 5) : (b : E) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff E p b).mp h
    have hle := Nat.le_of_dvd hb hd
    omega
  have h₂ : (2 : E) ≠ 0 := by simpa using small_ne 2 (by decide) (by decide)
  have h₃ : (3 : E) ≠ 0 := by simpa using small_ne 3 (by decide) (by decide)
  have hA : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ha
  change _ = recurrence (Fintype.card F) 0 n
  rcases Nat.even_or_odd n with hn | hn
  · rw [projective_card_eq F E hF₂ hE₂ h₂ h₃ hQ hn ha]
    obtain ⟨k, hk⟩ := hn
    have hN : n = 2 * k := by omega
    have hTotal : Module.finrank (ZMod p) E = 2 * (d * k) := by
      rw [hDegree, hN]
      ring
    have hNeg : (-(p : ℤ)) ^ d = -(Fintype.card F : ℤ) := by
      rw [hOdd.neg_pow]
      exact congrArg Neg.neg (by exact_mod_cast hCard.symm)
    have hPrime := actual_extension_trace_eq_recurrence_of_mod_two (E := E) hp hP
      (A := (1 : ZMod p)) one_ne_zero
    rw [paper5_traceCurve_trace_eq_zero hp hP one_ne_zero, prime_base_unit_curve p E,
      hTotal, zero_recurrence_at_even, pow_mul, hNeg] at hPrime
    rw [hN, zero_recurrence_at_even]
    exact hPrime
  · have hTotal : Odd (Module.finrank (ZMod p) E) := by rw [hDegree]; exact hOdd.mul hn
    rw [odd_extension_projective_count hP hTotal hE₂
      (shortCubic_discriminant_ne_zero h₂ h₃ hA)]
    obtain ⟨k, hk⟩ := hn
    have hN : n = 2 * k + 1 := by omega
    rw [hN, zero_recurrence_at_odd]
    push_cast
    ring

end
end ManuscriptAudit.Paper5RelativeNonsplitCounts

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5RelativeNonsplitCounts.signed_counts
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
