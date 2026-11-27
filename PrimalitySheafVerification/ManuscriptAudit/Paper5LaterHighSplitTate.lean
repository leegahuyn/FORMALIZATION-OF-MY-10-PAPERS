import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinatePreservingTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeventyNineFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNinetySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryOneHundredThreeFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryOneHundredNineFrobenius

/-! Native Tate coefficients for later A = 4 split rows using the actual coordinate twists. -/

namespace ManuscriptAudit.Paper5LaterHighSplitTate

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation
open CubicFrobeniusSexticTwists CubicRotationCombination PowerTateModule

noncomputable section

section P79

open Paper5OrdinarySeventyNineFrobenius

local instance : Fact (Nat.Prime 79) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 79) L] [CharP L 79] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_79 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 79) L 4))
      (endMap l (arithmeticFrobenius (ZMod 79) L 4)) = -13 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 79) L 4)) = 79 := by
  let z : L := algebraMap (ZMod 79) L (55 : ZMod 79)
  let n : Fin 3 := 1
  have h4 : (4 : ZMod 79) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 79) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 79) L)).mpr h4)
  have hq : Fintype.card (ZMod 79) = 6 * 13 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 79) ^ 13) ^ 2 = (55 : ZMod 79) ^ 1 := by decide
  have hy0 : ((4 : ZMod 79) ^ 13) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 79) L (parameter 1 4 13)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 79) L) hx0
  have hy : (algebraMap (ZMod 79) L (parameter 1 4 13)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 79) L) hy0
  have hF : arithmeticFrobenius (ZMod 79) L 1 = (3 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 79) L 1)) +
        (10 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = ((3 : ℕ) : ℤ) • (1 : AddMonoid.End (Points L)) +
      ((10 : ℕ) : ℤ) • rotation L
    simp only [negSucc_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 79) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy 3 10 hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P79

section P97

open Paper5OrdinaryNinetySevenFrobenius

local instance : Fact (Nat.Prime 97) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 97) L] [CharP L 97] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_97 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 97) L 4))
      (endMap l (arithmeticFrobenius (ZMod 97) L 4)) = 5 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 97) L 4)) = 97 := by
  let z : L := algebraMap (ZMod 97) L (61 : ZMod 97)
  let n : Fin 3 := 1
  have h4 : (4 : ZMod 97) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 97) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 97) L)).mpr h4)
  have hq : Fintype.card (ZMod 97) = 6 * 16 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 97) ^ 16) ^ 2 = (61 : ZMod 97) ^ 1 := by decide
  have hy0 : ((4 : ZMod 97) ^ 16) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 97) L (parameter 1 4 16)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 97) L) hx0
  have hy : (algebraMap (ZMod 97) L (parameter 1 4 16)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 97) L) hy0
  have hF : arithmeticFrobenius (ZMod 97) L 1 = (3 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 97) L 1)) +
        (-8 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = ((3 : ℕ) : ℤ) • (1 : AddMonoid.End (Points L)) +
      Int.negSucc 7 • rotation L
    simp only [negSucc_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 97) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy 3 (-8) hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P97

section P103

open Paper5OrdinaryOneHundredThreeFrobenius

local instance : Fact (Nat.Prime 103) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 103) L] [CharP L 103] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_103 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 103) L 4))
      (endMap l (arithmeticFrobenius (ZMod 103) L 4)) = -7 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 103) L 4)) = 103 := by
  let z : L := algebraMap (ZMod 103) L (56 : ZMod 103)
  let n : Fin 3 := 1
  have h4 : (4 : ZMod 103) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 103) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 103) L)).mpr h4)
  have hq : Fintype.card (ZMod 103) = 6 * 17 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 103) ^ 17) ^ 2 = (56 : ZMod 103) ^ 1 := by decide
  have hy0 : ((4 : ZMod 103) ^ 17) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 103) L (parameter 1 4 17)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 103) L) hx0
  have hy : (algebraMap (ZMod 103) L (parameter 1 4 17)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 103) L) hy0
  have hF : arithmeticFrobenius (ZMod 103) L 1 = (9 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 103) L 1)) +
        (-2 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = ((9 : ℕ) : ℤ) • (1 : AddMonoid.End (Points L)) +
      Int.negSucc 1 • rotation L
    simp only [negSucc_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 103) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy 9 (-2) hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P103

section P109

open Paper5OrdinaryOneHundredNineFrobenius

local instance : Fact (Nat.Prime 109) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 109) L] [CharP L 109] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_109 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 109) L 4))
      (endMap l (arithmeticFrobenius (ZMod 109) L 4)) = 2 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 109) L 4)) = 109 := by
  let z : L := algebraMap (ZMod 109) L (45 : ZMod 109)
  let n : Fin 3 := 0
  have h4 : (4 : ZMod 109) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 109) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 109) L)).mpr h4)
  have hq : Fintype.card (ZMod 109) = 6 * 18 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 109) ^ 18) ^ 2 = (45 : ZMod 109) ^ 0 := by decide
  have hy0 : ((4 : ZMod 109) ^ 18) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 109) L (parameter 1 4 18)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 109) L) hx0
  have hy : (algebraMap (ZMod 109) L (parameter 1 4 18)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 109) L) hy0
  have hF : arithmeticFrobenius (ZMod 109) L 1 = (-5 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 109) L 1)) +
        (-12 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = Int.negSucc 4 • (1 : AddMonoid.End (Points L)) +
      Int.negSucc 11 • rotation L
    simp only [negSucc_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 109) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy (-5) (-12) hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P109

end
end ManuscriptAudit.Paper5LaterHighSplitTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterHighSplitTate.trace_det_79,
      ``ManuscriptAudit.Paper5LaterHighSplitTate.trace_det_97,
      ``ManuscriptAudit.Paper5LaterHighSplitTate.trace_det_103,
      ``ManuscriptAudit.Paper5LaterHighSplitTate.trace_det_109] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
