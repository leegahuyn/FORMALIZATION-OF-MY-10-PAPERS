import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.CubicDoublingSurjective
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularUnitFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitAllPrimeAdic
import PrimalitySheafVerification.ManuscriptAudit.PrimeToCharacteristicTorsion

/-! Multiplication and torsion on actual geometric points of the supersingular unit curve. -/

namespace ManuscriptAudit.CubicSupersingularUnitTorsion

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicThreeTorsionCard CubicSupersingularUnitFrobenius
open CubicDoublingSurjective CubicTwoTorsionCard PrimeDivisibilityFromTorsionTower
open TorsionFrobeniusModule Paper5NonsplitPrimePowerCard WeierstrassAlgebraicPointFiniteOrder

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]

theorem multiplication_and_torsion (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    (n : ℕ) (hN : ¬ p ∣ n) :
    Function.Surjective (nsmulAddMonoidHom n : UnitPoints L →+ UnitPoints L) ∧
      Nat.card (Torsion n (UnitPoints L)) = n ^ 2 := by
  apply PrimeToCharacteristicTorsion.surjective_and_card (UnitPoints L) p _ n hN
  intro l hl hlp
  letI : Fact l.Prime := ⟨hl⟩
  by_cases h₂l : l = 2
  · subst l
    obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
    have h₂ : (2 : L) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂p
    have h₃ : (3 : L) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃p
    have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ (one_ne_zero : (1 : L) ≠ 0)
    refine ⟨affine_doubling_surjective h₂ h₃ one_ne_zero, ?_⟩
    have h := affineTwoTorsion_card h₂ h₃ one_ne_zero hΔ
    exact (Nat.card_congr (carrierEquiv 2 (UnitPoints L))).trans h
  · let W := Curve (1 : ZMod p)
    let G := (W.baseChange L).Point
    obtain ⟨hCard, hTrans⟩ := card_and_transition_surjective p L l hp hp₃ h₂l hlp
      (A := 1) one_ne_zero
    have hSurj : Function.Surjective (nsmulAddMonoidHom l : G →+ G) :=
      surjective_nsmul_of_surjective_transitions l G
        (exists_positive_nsmul_eq_zero (ZMod p) L W) hTrans
    have hCardLevel := hCard 1
    change Nat.card (Torsion (l ^ 1) G) = (l ^ 2) ^ 1 at hCardLevel
    rw [pow_one, pow_one] at hCardLevel
    have hCard₁ : Nat.card (Torsion l G) = l ^ 2 := hCardLevel
    let PropOn (V : Affine L) :=
      Function.Surjective (nsmulAddMonoidHom l : V.Point →+ V.Point) ∧
        Nat.card (Torsion l V.Point) = l ^ 2
    exact (congrArg PropOn (unit_baseChange (ZMod p) L)).mp ⟨hSurj, hCard₁⟩

end
end ManuscriptAudit.CubicSupersingularUnitTorsion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularUnitTorsion.multiplication_and_torsion
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
