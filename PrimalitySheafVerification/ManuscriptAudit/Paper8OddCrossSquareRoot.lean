import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossThreeBound

/-! Composite square-root cancellation for the manuscript's actual signed cross coefficient. -/

namespace ManuscriptAudit.Paper8OddCrossSquareRoot

open Paper8OddCrossThreeBound Paper8OddCrossCompositeBound Paper8OddCrossCuspRows Paper8OddCrossCuspCutoff

theorem chiFour_even_modulus {k : ℕ} (hk : k % 2 = 0) : chiFour (k : ZMod 4) = 0 := by
  have h1 : (k : ZMod 4) ≠ 1 := by
    change (k : ZMod 4) ≠ ((1 : ℕ) : ZMod 4)
    intro he
    have h := (ZMod.natCast_eq_natCast_iff' k 1 4).1 he
    omega
  have h3 : (k : ZMod 4) ≠ 3 := by
    change (k : ZMod 4) ≠ ((3 : ℕ) : ZMod 4)
    intro he
    have h := (ZMod.natCast_eq_natCast_iff' k 3 4).1 he
    omega
  simp [chiFour, h1, h3]

theorem norm_crossSum_squareRoot {k : ℕ} (hk : 0 < k) :
    ‖crossSum hk‖ ≤ (2 : ℝ) ^ k.primeFactors.card * Real.sqrt (k : ℝ) := by
  letI : NeZero k := ⟨hk.ne'⟩
  by_cases he : k % 2 = 0
  · rw [crossSum_eq, chiFour_even_modulus he, Int.cast_zero, zero_mul, norm_zero]
    positivity
  · have ho : k % 2 = 1 := by omega
    by_cases h3 : 3 ∣ k
    · exact norm_oddCrossSum_three_divides ho h3
    · have h2 : ¬ 2 ∣ k := fun hd => he (Nat.mod_eq_zero_of_dvd hd)
      have hC : k.Coprime 6 := by
        rw [show (6 : ℕ) = 2 * 3 by decide, Nat.coprime_mul_iff_right]
        exact ⟨(Nat.prime_two.coprime_iff_not_dvd.2 h2).symm,
          (Nat.prime_three.coprime_iff_not_dvd.2 h3).symm⟩
      exact norm_oddCrossSum_coprime_six hC

end ManuscriptAudit.Paper8OddCrossSquareRoot

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossSquareRoot.norm_crossSum_squareRoot
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
