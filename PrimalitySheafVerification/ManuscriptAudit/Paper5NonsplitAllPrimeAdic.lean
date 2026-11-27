import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly
import PrimalitySheafVerification.ManuscriptAudit.FirstPrimeTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitPrimePowerCard
import PrimalitySheafVerification.ManuscriptAudit.PrimeDivisibilityFromTorsionTower
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAlgebraicPointFiniteOrder

/-! The full actual prime-adic determinant and characteristic polynomial at all l≠p. -/

namespace ManuscriptAudit.Paper5NonsplitAllPrimeAdic

open Polynomial Module WeierstrassCurve CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicNonsplitPrimeAdicFrobenius CubicNonsplitTwoThreeAdicCharpoly
open PowerTateModule PowerTateRankTwo Paper5NonsplitFrobeniusModFour
open Paper5NonsplitPrimePowerCard PrimeDivisibilityFromTorsionTower
open WeierstrassAlgebraicPointFiniteOrder

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

def actualBasis (hp : 5 ≤ p) (hq : p % 3 = 2) (hlp : l ≠ p) {A : ZMod p} (hA : A ≠ 0) :
    Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  by_cases hl : l = 2
  · subst l
    exact twoAdicBasis (ZMod p) L h₂ h₃ hA
  · let G := Points p L A
    obtain ⟨hCard, hTrans⟩ := card_and_transition_surjective p L l hp hq hl hlp hA
    have hDiv : Function.Surjective (fun P : G => l • P) :=
      surjective_nsmul_of_surjective_transitions l G
        (exists_positive_nsmul_eq_zero (ZMod p) L (Curve A)) hTrans
    let B := FirstPrimeTorsionBasis.basis l G (by simpa only [pow_one] using hCard 1)
    let V (W : Affine L) := Basis (Fin 2) ℤ_[l] (Tate l W.Point)
    have hW : (Curve A).baseChange L = Curve (algebraMap (ZMod p) L A) :=
      CubicNonsplitFrobeniusTrace.centered_baseChange (ZMod p) L A
    exact Eq.mp (congrArg V hW) ((Basis.finTwoProd ℤ_[l]).map (padicPairEquiv l G B hDiv))

private theorem odd_field_card (hp : 5 ≤ p) : Fintype.card (ZMod p) % 2 = 1 := by
  apply FiniteField.odd_card_of_char_ne_two
  rw [ringChar.eq (ZMod p) p]
  omega

/-- The nonsplit centered cubic has exact determinant p for every coefficient prime different from p. -/
theorem determinant (hp : 5 ≤ p) (hq : p % 3 = 2) (hlp : l ≠ p) {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.det (Action (ZMod p) L l A) = (p : ℤ_[l]) := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have hq3 : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hq
  simpa only [ZMod.card] using determinant_eq_card (ZMod p) L l h₂ h₃ hA hq3
    (odd_field_card p hp) (actualBasis p L l hp hq hlp hA)

/-- The actual characteristic polynomial is T²+p for every prime l≠p. -/
theorem charpoly (hp : 5 ≤ p) (hq : p % 3 = 2) (hlp : l ≠ p) {A : ZMod p} (hA : A ≠ 0) :
    letI := Module.Free.of_basis (actualBasis p L l hp hq hlp hA)
    letI := Module.Finite.of_basis (actualBasis p L l hp hq hlp hA)
    (Action (ZMod p) L l A).charpoly = X ^ 2 + C (p : ℤ_[l]) := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have hq3 : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hq
  simpa only [ZMod.card] using charpoly_eq (ZMod p) L l h₂ h₃ hA hq3
    (odd_field_card p hp) (actualBasis p L l hp hq hlp hA)

end
end ManuscriptAudit.Paper5NonsplitAllPrimeAdic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitAllPrimeAdic.actualBasis,
      ``ManuscriptAudit.Paper5NonsplitAllPrimeAdic.determinant,
      ``ManuscriptAudit.Paper5NonsplitAllPrimeAdic.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
