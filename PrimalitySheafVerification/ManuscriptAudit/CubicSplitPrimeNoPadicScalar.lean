import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.PadicNoPrimitiveCube
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiEisenstein
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour

/-! The arithmetic characteristic polynomial of a good split prime-field reduction is not scalar. -/

namespace ManuscriptAudit.CubicSplitPrimeNoPadicScalar

open FiniteFieldPointCount CubicJacobiEisenstein CubicThreeTorsionCard
open Paper5NonsplitFrobeniusModFour
open scoped Padic

variable (p : ℕ) [Fact p.Prime]

/-- At every good split prime and every nonzero twist, the native arithmetic polynomial
has no scalar root in either of the two true Tate coefficient rings. -/
theorem no_scalar_root (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) (r : ℤ_[l]) :
    let t : ℤ := (p : ℤ) + 1 - Nat.card (shortCubic (0 : ZMod p) A).toProjective.Point
    r ^ 2 - (t : ℤ_[l]) * r + (p : ℤ_[l]) ≠ 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ringChar.eq (ZMod p) p]; omega
  have hsplit : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  obtain ⟨a, b, ht, hn⟩ := exists_integral_trace_norm hchar hsplit hA
    (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  rw [ZMod.card] at ht hn
  have hb : b ≠ 0 := by
    intro he
    have hSq : (p : ℤ) = a ^ 2 := by simpa [he] using hn
    have hSP : a.natAbs ^ 2 = p := by
      simpa only [Int.natAbs_natCast, Int.natAbs_pow] using (congrArg Int.natAbs hSq).symm
    have hPrime : p.Prime := Fact.out
    have hTwo := ((hPrime.pow_eq_iff).mp hSP).2
    omega
  dsimp only
  rw [ht, ← Int.cast_natCast, hn]
  exact PadicNoPrimitiveCube.no_scalar_root l hl a b hb r

end ManuscriptAudit.CubicSplitPrimeNoPadicScalar

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitPrimeNoPadicScalar.no_scalar_root
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
