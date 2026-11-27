import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicHermitianFrobeniusSquare
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour

/-! The actual degree-4k Frobenius iterate is scalar on geometric points. -/

namespace ManuscriptAudit.Paper5NonsplitQuarticIterate

open WeierstrassCurve CubicThreeTorsionOrdinate WeierstrassFrobeniusFixed
open CubicHermitianFrobeniusSquare Paper5NonsplitFrobeniusModFour

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

theorem quartic_iterate (hp : 5 ≤ p) (hq : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (k : ℕ) (P : ((Curve A).baseChange L).Point) :
    ((⇑(frobeniusOnPoints p L (Curve A)))^[4 * k]) P = (p ^ (2 * k)) • P := by
  let f := frobeniusOnPoints p L (Curve A)
  have h₂ := (small_char p (ZMod p) hp).1
  have h₃ := (small_char p (ZMod p) hp).2
  have hq3 : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hq
  have hq2 : Fintype.card (ZMod p) % 2 = 1 := by
    apply FiniteField.odd_card_of_char_ne_two
    rw [ringChar.eq (ZMod p) p]
    omega
  have hTwo (Q : ((Curve A).baseChange L).Point) : f (f Q) = -(p • Q) := by
    simpa only [f, frobeniusOnPoints, ZMod.card] using
      frobenius_sq_eq_neg_card (ZMod p) L h₂ h₃ hA hq3 hq2 Q
  have hFour (Q : ((Curve A).baseChange L).Point) : ((⇑f)^[4]) Q = p ^ 2 • Q := by
    change f (f (f (f Q))) = _
    rw [hTwo (f (f Q)), hTwo Q, smul_neg, neg_neg, pow_two, mul_nsmul]
  change ((⇑f)^[4 * k]) P = _
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 + 4 * k by omega, Function.iterate_add_apply,
      hFour, ih, ← mul_nsmul', ← pow_add]
    rw [show 2 + 2 * k = 2 * (k + 1) by omega]

end
end ManuscriptAudit.Paper5NonsplitQuarticIterate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5NonsplitQuarticIterate.quartic_iterate
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
