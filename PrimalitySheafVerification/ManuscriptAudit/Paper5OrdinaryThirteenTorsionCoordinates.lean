import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTorsionKernel
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra

/-! The actual nonzero ordinary thirteen-torsion points are the quadratic coordinate fibers. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenTorsionCoordinates

open WeierstrassCurve CubicThreeTorsionOrdinate CubicTwoTorsion CubicThreeTorsion CubicTriplingCoordinates
open Paper5OrdinaryThirteenAlgebra Paper5OrdinaryThirteenCoordinates Paper5OrdinaryThirteenSecant
open Paper5OrdinaryThirteenTorsionAlgebra Paper5OrdinaryThirteenTorsionKernel

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]

private theorem rotation_square_some {x y : L} (hP : (Curve (1 : L)).Nonsingular x y) :
    ∃ h' : (Curve (1 : L)).Nonsingular (9 * x) y,
      rotation L (rotation L (Affine.Point.some x y hP)) = Affine.Point.some (9 * x) y h' := by
  obtain ⟨h₁, he₁⟩ := rotation_some L hP
  obtain ⟨h₂, he₂⟩ := rotation_some L h₁
  have hX : (3 : L) * (3 * x) = 9 * x := by ring
  have h' : (Curve (1 : L)).Nonsingular (9 * x) y := by simpa only [hX] using h₂
  refine ⟨h', (congrArg (rotation L) he₁).trans (he₂.trans ?_)⟩
  rw [Affine.Point.some.injEq]
  exact ⟨hX, rfl⟩

set_option maxHeartbeats 1000000 in
/-- At an actual finite point, thirteen-torsion is exactly the quadratic equation in x³. -/
theorem torsion_some_iff {x y : L} (hP : (Curve (1 : L)).Nonsingular x y) :
    (13 : ℕ) • (Affine.Point.some x y hP : Points L) = 0 ↔ torsionQuadratic (x ^ 3) = 0 := by
  let P : Points L := .some x y hP
  have h₂ : (2 : L) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₃ : (3 : L) ≠ 0 := numeral_ne_zero 3 (by decide)
  have h₈ : (8 : L) ≠ 0 := numeral_ne_zero 8 (by decide)
  have he := (nonsingular_iff (discriminant_ne_zero L) x y).mp hP
  obtain ⟨hR, eR₀⟩ := rotation_square_some L hP
  have eR : rotation L (rotation L P) = Affine.Point.some (9 * x) y hR := eR₀
  change (13 : ℕ) • P = 0 ↔ _
  rw [torsion_iff L P]
  constructor
  · intro heq
    have hx : x ≠ 0 := by
      intro hx
      have hRot : rotation L (rotation L P) = P := by
        refine eR.trans ?_
        change Affine.Point.some (9 * x) y hR = Affine.Point.some x y hP
        rw [Affine.Point.some.injEq]
        exact ⟨by simp [hx], rfl⟩
      have h : (3 : ℕ) • P = P := heq.trans hRot
      rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, one_nsmul] at h
      have hz : (2 : ℕ) • P = 0 := add_right_cancel (h.trans (zero_add P).symm)
      have hY := (two_nsmul_affine_some_iff h₂ hP).mp hz
      exact zero_ne_one (by
        simpa only [hY, hx, zero_pow (by decide : (2 : ℕ) ≠ 0),
          zero_pow (by decide : (3 : ℕ) ≠ 0), zero_add] using he)
    have hy : y ≠ 0 := by
      intro hy
      have hz : (2 : ℕ) • P = 0 := (two_nsmul_affine_some_iff h₂ hP).mpr hy
      have hThree : (3 : ℕ) • P = P := by
        rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, one_nsmul, hz, zero_add]
      have hPoint : Affine.Point.some x y hP = Affine.Point.some (9 * x) y hR :=
        hThree.symm.trans (heq.trans eR)
      have hXY : x = 9 * x ∧ y = y := by simpa only [Affine.Point.some.injEq] using hPoint
      exact (mul_ne_zero h₈ hx) (by linear_combination -hXY.1)
    have hg : x ^ 3 + 4 ≠ 0 := by
      intro hg
      have hz : (3 : ℕ) • P = 0 :=
        (three_nsmul_affine_some_iff h₂ h₃ (discriminant_ne_zero L) hP).mpr
          ⟨hy, by rw [mul_one, hg, mul_zero]⟩
      exact Affine.Point.some_ne_zero hR (eR.symm.trans (heq.symm.trans hz))
    obtain ⟨hT, eT₀⟩ := triple_some_coordinates h₂ h₃ (discriminant_ne_zero L)
      hy hx (by simpa only [mul_one] using hg) (tripleX_correct hx hg) hP
    have hT' : (Curve (1 : L)).Nonsingular (tripleX x) (tripleY x y) := hT
    have eT : (3 : ℕ) • P = Affine.Point.some (tripleX x) (tripleY x y) hT' := eT₀
    have hXY : tripleX x = 9 * x ∧ tripleY x y = y := by
      simpa only [Affine.Point.some.injEq] using eT.symm.trans (heq.trans eR)
    exact (tripleY_eq_iff_quadratic hx hy hg he hXY.1).mp hXY.2
  · intro hquad
    obtain ⟨hx₀, hy₀, hg⟩ := torsionQuadratic_nonzero_values hquad
    have hx : x ≠ 0 := fun h => hx₀ (by simp [h])
    have hy : y ≠ 0 := fun h => hy₀ (by simp [h] at he; exact he.symm)
    have hX := tripleX_of_quadratic hquad
    have hY := (tripleY_eq_iff_quadratic hx hy hg he hX).mpr hquad
    obtain ⟨hT, eT₀⟩ := triple_some_coordinates h₂ h₃ (discriminant_ne_zero L)
      hy hx (by simpa only [mul_one] using hg) (tripleX_correct hx hg) hP
    have hT' : (Curve (1 : L)).Nonsingular (tripleX x) (tripleY x y) := hT
    have eT : (3 : ℕ) • P = Affine.Point.some (tripleX x) (tripleY x y) hT' := eT₀
    have hPoint : Affine.Point.some (tripleX x) (tripleY x y) hT' =
        Affine.Point.some (9 * x) y hR := by
      rw [Affine.Point.some.injEq]
      exact ⟨hX, hY⟩
    exact eT.trans (hPoint.trans eR.symm)

end
end ManuscriptAudit.Paper5OrdinaryThirteenTorsionCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionCoordinates.torsion_some_iff
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
