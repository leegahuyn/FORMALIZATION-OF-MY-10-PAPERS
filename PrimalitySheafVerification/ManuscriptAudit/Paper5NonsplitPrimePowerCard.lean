import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusOrderValuations
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitPrimePowerFixedCard
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTailCard

/-! Native odd-prime torsion of the nonsplit cubic, at every level. -/

namespace ManuscriptAudit.Paper5NonsplitPrimePowerCard

open Polynomial WeierstrassCurve CubicThreeTorsionOrdinate
open FrobeniusOrderValuations Paper5NonsplitPrimePowerFixedCard
open PowerTorsionTower PowerTorsionTailCard

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

abbrev Points (A : ZMod p) := ((Curve A).baseChange L).Point

theorem eventual_card (hp : 5 ≤ p) (hq : p % 3 = 2) (hl₂ : l ≠ 2) (hlp : l ≠ p)
    {A : ZMod p} (hA : A ≠ 0) :
    ∃ N, ∀ n, N ≤ n → Nat.card (PowerTorsion l (Points p L A) n) = (l ^ 2) ^ n := by
  classical
  have hP : p.Prime := Fact.out
  have hL : l.Prime := Fact.out
  have hPow : 1 < p ^ 2 := by
    simpa only [one_pow] using Nat.pow_lt_pow_left hP.one_lt (by decide : (2 : ℕ) ≠ 0)
  have hNot : ¬l ∣ p ^ 2 := fun h =>
    hlp ((Nat.prime_dvd_prime_iff_eq hL hP).mp (hL.dvd_of_dvd_pow h))
  obtain ⟨N, hN⟩ := eventually_exists_exact_factor l (p ^ 2) (hL.odd_of_ne_two hl₂) hPow hNot
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, d, hk, hfactor, hd⟩ := hN n hn
  let E := GaloisField p (4 * k)
  letI : Fintype E := Fintype.ofFinite E
  have hDegree : Module.finrank (ZMod p) E = 4 * k :=
    GaloisField.finrank p (n := 4 * k) (Nat.mul_ne_zero (by decide) hk.ne')
  letI : Algebra.IsAlgebraic (ZMod p) E := ⟨fun x => ⟨
    (X ^ Fintype.card E - X : (ZMod p)[X]),
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card,
    by simp [FiniteField.pow_card]⟩⟩
  let i : E →ₐ[ZMod p] L := IsAlgClosed.lift
  exact card_at_exact_factor p L E l hp hq hA i hDegree n d
    (by simpa only [← pow_mul] using hfactor) hd

theorem card_and_transition_surjective (hp : 5 ≤ p) (hq : p % 3 = 2)
    (hl₂ : l ≠ 2) (hlp : l ≠ p) {A : ZMod p} (hA : A ≠ 0) :
    (∀ n, Nat.card (PowerTorsion l (Points p L A) n) = (l ^ 2) ^ n) ∧
      ∀ n, Function.Surjective (transition l (Points p L A) n) := by
  obtain ⟨N, hN⟩ := eventual_card p L l hp hq hl₂ hlp hA
  exact card_and_surjective_of_eventually_exact l (Points p L A) (pow_pos (Fact.out : l.Prime).pos _) hN

end
end ManuscriptAudit.Paper5NonsplitPrimePowerCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitPrimePowerCard.eventual_card,
      ``ManuscriptAudit.Paper5NonsplitPrimePowerCard.card_and_transition_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
