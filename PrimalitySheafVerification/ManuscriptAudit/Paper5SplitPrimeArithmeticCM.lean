import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiEisenstein
import PrimalitySheafVerification.ManuscriptAudit.PrimeCubicCMOrientation
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! The split-prime paper fiber has a unique oriented pair of integer point-count coefficients. -/

namespace ManuscriptAudit.Paper5SplitPrimeArithmeticCM

open FiniteFieldPointCount CubicThreeTorsionCard CubicJacobiEisenstein PrimeCubicCMOrientation
open Paper5NonsplitFrobeniusModFour
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- For each primitive cube root in the prime field, exactly one integral pair has the signed
count, norm p, and zero reduction at that root. -/
theorem exists_unique_coefficients (hp : 5 ≤ p) (hsplit : p % 3 = 1) {A z : ZMod p}
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) :
    ∃! ab : ℤ × ℤ,
      (p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ) =
        2 * ab.1 - ab.2 ∧
      ab.1 ^ 2 - ab.1 * ab.2 + ab.2 ^ 2 = (p : ℤ) ∧
      (ab.1 : ZMod p) + (ab.2 : ZMod p) * z = 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ringChar.eq (ZMod p) p]; omega
  have hdiv : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have he := exists_integral_trace_norm hchar hdiv hA (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  apply exists_unique_zero_reduction p hz
  obtain ⟨a, b, ht, hn⟩ := he
  have hcurve : shortCubic (0 : ZMod p) A = paper5TraceCurve p A := by
    ext <;> simp [shortCubic, paper5TraceCurve]
  rw [ZMod.card, hcurve] at ht
  exact ⟨a, b, ht, by simpa only [ZMod.card] using hn.symm⟩

end
end ManuscriptAudit.Paper5SplitPrimeArithmeticCM

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5SplitPrimeArithmeticCM.exists_unique_coefficients
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
