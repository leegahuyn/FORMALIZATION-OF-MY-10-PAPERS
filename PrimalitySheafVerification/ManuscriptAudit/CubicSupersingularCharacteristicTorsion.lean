import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricScaling
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularUnitFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitCharacteristicTorsion

/-! Characteristic-primary torsion on every centered geometric twist. -/

namespace ManuscriptAudit.CubicSupersingularCharacteristicTorsion

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicSupersingularUnitFrobenius CubicGeometricScaling TorsionFrobeniusModule
open PowerTorsionTower PowerTateModule

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

theorem geometric_p_power_eq_zero (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    {A : L} (hA : A ≠ 0) (n : ℕ) {P : (Curve A).Point} (hP : (p ^ n) • P = 0) :
    P = 0 := by
  obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂p
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃p
  let Good (V : Affine L) := ∀ P : V.Point, (p ^ n) • P = 0 → P = 0
  have hPrime : Good ((Curve (1 : ZMod p)).baseChange L) :=
    fun _ h => Paper5NonsplitCharacteristicTorsion.p_power_smul_eq_zero p L hp hp₃ one_ne_zero n h
  have hUnit : Good (Curve (1 : L)) := (congrArg Good (unit_baseChange (ZMod p) L)).mp hPrime
  obtain ⟨e⟩ := exists_scaleEquiv (one_ne_zero : (1 : L) ≠ 0) hA
    (shortCubic_discriminant_ne_zero h₂ h₃ one_ne_zero)
    (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  have h0 : (p ^ n) • e.symm P = 0 := by rw [← map_nsmul, hP, map_zero]
  apply e.symm.injective
  rw [map_zero]
  exact hUnit (e.symm P) h0

theorem geometric_level_card (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    {A : L} (hA : A ≠ 0) (n : ℕ) : Nat.card (PowerTorsion p (Curve A).Point n) = 1 := by
  letI : Unique (PowerTorsion p (Curve A).Point n) := ⟨⟨0⟩, fun P => Subtype.ext (by
    change (P : (Curve A).Point) = 0
    exact geometric_p_power_eq_zero p L hp hp₃ hA n ((mem_iff _ _ _).mp P.property))⟩
  exact Nat.card_unique

theorem geometric_characteristic_tate_subsingleton (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    {A : L} (hA : A ≠ 0) : Subsingleton (Tate p (Curve A).Point) := by
  refine ⟨fun x y => PowerTateModule.ext p _ (fun n => Subtype.ext ?_)⟩
  have hX := geometric_p_power_eq_zero p L hp hp₃ hA n
    ((mem_iff _ _ _).mp (evaluate p _ n x).property)
  have hY := geometric_p_power_eq_zero p L hp hp₃ hA n
    ((mem_iff _ _ _).mp (evaluate p _ n y).property)
  exact hX.trans hY.symm

end
end ManuscriptAudit.CubicSupersingularCharacteristicTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSupersingularCharacteristicTorsion.geometric_p_power_eq_zero,
      ``ManuscriptAudit.CubicSupersingularCharacteristicTorsion.geometric_level_card,
      ``ManuscriptAudit.CubicSupersingularCharacteristicTorsion.geometric_characteristic_tate_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
