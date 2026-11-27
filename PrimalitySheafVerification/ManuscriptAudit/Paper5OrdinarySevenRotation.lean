import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenGeometry
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenSecant
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! The native ordinary seven rotation is nonscalar on both first torsion levels. -/

namespace ManuscriptAudit.Paper5OrdinarySevenRotation

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsion
open CubicThreeTorsionOrdinate CubicThreeTorsionCard
open Paper5OrdinarySeven Paper5OrdinarySevenGeometry Paper5OrdinarySevenSecant
open TorsionFrobeniusModule PowerTorsionTower

noncomputable section

variable (L : Type*) [Field L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]

local notation "W" => (ordinaryCurve L).toAffine

theorem ordinary_eq_centered : W = Curve (5 : L) := by
  simp [ordinaryCurve, Curve, CubicAffine, shortCubic]

theorem three_ne : (3 : L) ≠ 0 := by
  change ((3 : ℕ) : L) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff L 7 3]
  decide

theorem five_ne : (5 : L) ≠ 0 := by
  change ((5 : ℕ) : L) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff L 7 5]
  decide

private theorem some_nsmul_three {y : L} (hy : y ≠ 0) (h : W.Nonsingular 1 y) :
    (3 : ℕ) • (Affine.Point.some 1 y h : W.Point) = 0 := by
  let Q (C : Affine L) : Prop := ∀ h : C.Nonsingular 1 y,
    (3 : ℕ) • (Affine.Point.some 1 y h : C.Point) = 0
  have hQ : Q (Curve (5 : L)) := fun hp =>
    (three_nsmul_affine_some_iff two_ne (three_ne L)
      (shortCubic_discriminant_ne_zero two_ne (three_ne L) (five_ne L)) hp).mpr
      ⟨hy, by linear_combination (3 : L) * seven_zero L⟩
  exact (Eq.mpr (congrArg Q (ordinary_eq_centered L)) hQ) h

set_option maxHeartbeats 1200000 in
theorem not_scalar_two :
    ¬∃ c : ZMod (2 ^ 1), mapLinear (2 ^ 1) (rotation L) =
      c • (1 : Module.End (ZMod (2 ^ 1)) (PowerTorsion 2 (Points L) 1)) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-(5 : L)) zero_lt_three
  have hx₀ : x ≠ 0 := by
    intro h
    exact five_ne L (by simpa [h] using hx.symm)
  have hP : W.Nonsingular x 0 :=
    Affine.equation_iff_nonsingular.mp ((equation_iff L x 0).mpr (by simp [hx]))
  let P : W.Point := .some x 0 hP
  have hTwo : (2 : ℕ) • P = 0 := by
    change (2 : ℕ) • (Affine.Point.some x 0 hP : W.Point) = _
    rw [two_nsmul, Affine.Point.add_self_of_Y_eq (by rw [negY_eq, neg_zero])]
  let Q : PowerTorsion 2 (Points L) 1 := ⟨P, (mem_iff _ _ _).mpr (by simpa only [pow_one] using hTwo)⟩
  have he := congrArg (fun f : Module.End (ZMod (2 ^ 1)) (PowerTorsion 2 (Points L) 1) =>
    (f Q : Points L)) hc
  change rotation L P = ((c • Q : PowerTorsion 2 (Points L) 1) : Points L) at he
  rcases (by decide : ∀ a : ZMod (2 ^ 1), a = 0 ∨ a = 1) c with h | h
  · rw [h, zero_smul] at he
    change rotation L (Affine.Point.some x 0 hP) = 0 at he
    rw [rotation_some] at he
    exact Affine.Point.some_ne_zero _ he
  · rw [h, one_smul] at he
    change rotation L (Affine.Point.some x 0 hP) = Affine.Point.some x 0 hP at he
    rw [rotation_some, Affine.Point.some.injEq] at he
    exact hx₀ (by linear_combination he.1)

set_option maxHeartbeats 1200000 in
theorem not_scalar_three :
    ¬∃ c : ZMod (3 ^ 1), mapLinear (3 ^ 1) (rotation L) =
      c • (1 : Module.End (ZMod (3 ^ 1)) (PowerTorsion 3 (Points L) 1)) := by
  rintro ⟨c, hc⟩
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (6 : L) zero_lt_two
  have hy₀ : y ≠ 0 := by
    intro h
    apply (one_ne_zero : (1 : L) ≠ 0)
    have hy' : (0 : L) = 6 := by simpa [h] using hy
    linear_combination hy' + seven_zero L
  have hP : W.Nonsingular 1 y :=
    Affine.equation_iff_nonsingular.mp ((equation_iff L 1 y).mpr (by norm_num [hy]))
  let P : W.Point := .some 1 y hP
  have hThree : (3 : ℕ) • P = 0 := some_nsmul_three L hy₀ hP
  have hTwo : (2 : ℕ) • P = -P := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, one_nsmul] using hThree
  let Q : PowerTorsion 3 (Points L) 1 := ⟨P, (mem_iff _ _ _).mpr (by simpa only [pow_one] using hThree)⟩
  have he := congrArg (fun f : Module.End (ZMod (3 ^ 1)) (PowerTorsion 3 (Points L) 1) =>
    (f Q : Points L)) hc
  change rotation L P = ((c • Q : PowerTorsion 3 (Points L) 1) : Points L) at he
  rcases (by decide : ∀ a : ZMod (3 ^ 1), a = 0 ∨ a = 1 ∨ a = 2) c with h | h | h
  · rw [h, zero_smul] at he
    change rotation L (Affine.Point.some 1 y hP) = 0 at he
    rw [rotation_some] at he
    exact Affine.Point.some_ne_zero _ he
  · rw [h, one_smul] at he
    change rotation L (Affine.Point.some 1 y hP) = Affine.Point.some 1 y hP at he
    rw [rotation_some, Affine.Point.some.injEq] at he
    exact (one_ne_zero : (1 : L) ≠ 0) (by linear_combination he.1)
  · rw [h] at he
    have hs : (2 : ZMod (3 ^ 1)) • Q = (2 : ℕ) • Q := by
      change ((2 : ℕ) : ZMod (3 ^ 1)) • Q = (2 : ℕ) • Q
      rw [Nat.cast_smul_eq_nsmul]
    rw [hs] at he
    change rotation L P = (2 : ℕ) • P at he
    rw [hTwo] at he
    change rotation L (Affine.Point.some 1 y hP) = -Affine.Point.some 1 y hP at he
    rw [rotation_some, Affine.Point.neg_some, Affine.Point.some.injEq] at he
    exact (one_ne_zero : (1 : L) ≠ 0) (by linear_combination he.1)

end
end ManuscriptAudit.Paper5OrdinarySevenRotation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenRotation.ordinary_eq_centered,
      ``ManuscriptAudit.Paper5OrdinarySevenRotation.not_scalar_two,
      ``ManuscriptAudit.Paper5OrdinarySevenRotation.not_scalar_three] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
