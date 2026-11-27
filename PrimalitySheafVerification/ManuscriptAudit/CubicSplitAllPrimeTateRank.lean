import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitLangKernelRank
import PrimalitySheafVerification.ManuscriptAudit.PowerTateRankTwo

/-! For every coefficient prime away from the base prime, the actual split centered cubic has rank-two Tate module. -/

namespace ManuscriptAudit.CubicSplitAllPrimeTateRank

open Module CubicCertifiedInertTate CubicSplitAllInertTate CubicNonsplitThreeAdicTrace
open PowerTorsionTower PowerTateModule PowerTateRankTwo
open scoped Padic

noncomputable section

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L]
  [DecidableEq L] [IsAlgClosed L]

/-- Every native finite level is square-order and every adjacent transition is onto. -/
theorem card_and_transition (c : IntegralReference p L) (l : ℕ) [Fact l.Prime] (hl : p ≠ l) :
    (∀ n, Nat.card (PowerTorsion l (Points c) n) = (l ^ 2) ^ n) ∧
      ∀ n, Function.Surjective (transition l (Points c) n) := by
  have hp : p.Prime := Fact.out
  have hL : l.Prime := Fact.out
  have hc := (Nat.coprime_primes hp hL).mpr hl
  have hs := CubicSplitScalarSurjectivity.scalar_surjective_of_reference c hL.ne_zero hc
  refine ⟨fun n => ?_, fun n => transition_surjective l (Points c) hs n⟩
  rw [card_powerTorsion l (Points c) hs, CubicSplitLangKernelRank.card_first c l hl]

/-- A basis on the full native inverse-limit Tate module, for all primes l≠p. -/
def basis (c : IntegralReference p L) (l : ℕ) [Fact l.Prime] (hl : p ≠ l) :
    Basis (Fin 2) ℤ_[l] (Tate l (Points c)) := by
  have hp : p.Prime := Fact.out
  have hL : l.Prime := Fact.out
  have hc := (Nat.coprime_primes hp hL).mpr hl
  have hs := CubicSplitScalarSurjectivity.scalar_surjective_of_reference c hL.ne_zero hc
  let B := FirstPrimeTorsionBasis.basis l (Points c) (by
    simpa only [pow_one] using (card_and_transition c l hl).1 1)
  exact (Basis.finTwoProd ℤ_[l]).map (padicPairEquiv l (Points c) B hs)

/-- A literal rank-two Tate basis for all good split prime-field models. -/
def nativeBasis {L : Type} [Field L] [Algebra (ZMod p) L] [DecidableEq L] [IsAlgClosed L]
    (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : p ≠ l) :
    Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) :=
  basis (reference p L hp hs hA) l hl

end

end ManuscriptAudit.CubicSplitAllPrimeTateRank

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicSplitAllPrimeTateRank.card_and_transition,
      ``ManuscriptAudit.CubicSplitAllPrimeTateRank.basis,
      ``ManuscriptAudit.CubicSplitAllPrimeTateRank.nativeBasis] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
