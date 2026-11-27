import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinatePreservingTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySixtyOneFrobenius

/-! Exact native Tate coefficients for the later A = 4 entries at 37 and 61. -/

namespace ManuscriptAudit.Paper5LaterFirstSplitTate

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation CubicDoublingCoordinates
open CubicFrobeniusSexticTwists CubicRotationCombination PowerTateModule

noncomputable section

section P37

open Paper5OrdinaryThirtySevenFrobenius

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 37) L] [CharP L 37] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_37 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 37) L 4))
      (endMap l (arithmeticFrobenius (ZMod 37) L 4)) = -1 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 37) L 4)) = 37 := by
  let z : L := algebraMap (ZMod 37) L (10 : ZMod 37)
  let n : Fin 3 := 1
  have h4 : (4 : ZMod 37) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 37) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 37) L)).mpr h4)
  have hq : Fintype.card (ZMod 37) = 6 * 6 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 37) ^ 6) ^ 2 = (10 : ZMod 37) ^ 1 := by decide
  have hy0 : ((4 : ZMod 37) ^ 6) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 37) L (parameter 1 4 6)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 37) L) hx0
  have hy : (algebraMap (ZMod 37) L (parameter 1 4 6)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 37) L) hy0
  have hF : arithmeticFrobenius (ZMod 37) L 1 = (-3 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 37) L 1)) +
        (4 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = Int.negSucc 2 • (1 : AddMonoid.End (Points L)) +
      ((4 : ℕ) : ℤ) • rotation L
    rw [negSucc_zsmul, natCast_zsmul]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 37) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy (-3) 4 hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P37

section P61

open Paper5OrdinarySixtyOneFrobenius

local instance : Fact (Nat.Prime 61) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 61) L] [CharP L 61] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_61 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 61) L 4))
      (endMap l (arithmeticFrobenius (ZMod 61) L 4)) = -13 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 61) L 4)) = 61 := by
  let z : L := algebraMap (ZMod 61) L (47 : ZMod 61)
  let n : Fin 3 := 2
  have h4 : (4 : ZMod 61) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 61) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 61) L)).mpr h4)
  have hq : Fintype.card (ZMod 61) = 6 * 10 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 61) ^ 10) ^ 2 = (47 : ZMod 61) ^ 2 := by decide
  have hy0 : ((4 : ZMod 61) ^ 10) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 61) L (parameter 1 4 10)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 61) L) hx0
  have hy : (algebraMap (ZMod 61) L (parameter 1 4 10)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 61) L) hy0
  have hF : arithmeticFrobenius (ZMod 61) L 1 = (5 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 61) L 1)) +
        (-4 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = ((5 : ℕ) : ℤ) • (1 : AddMonoid.End (Points L)) +
      Int.negSucc 3 • rotation L
    rw [natCast_zsmul, negSucc_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 61) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy 5 (-4) hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P61

end
end ManuscriptAudit.Paper5LaterFirstSplitTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterFirstSplitTate.trace_det_37,
      ``ManuscriptAudit.Paper5LaterFirstSplitTate.trace_det_61] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
