import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinatePreservingTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOneFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryFortyThreeFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySixtySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeventyThreeFrobenius

/-! Native Tate coefficients for later A = 4 split rows using the actual coordinate twists. -/

namespace ManuscriptAudit.Paper5LaterMidSplitTate

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation
open CubicFrobeniusSexticTwists CubicRotationCombination PowerTateModule

noncomputable section

section P31

open Paper5OrdinaryThirtyOneFrobenius Paper5OrdinaryThirtyOneCoordinates

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 31) L] [CharP L 31] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_31 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 31) L 4))
      (endMap l (arithmeticFrobenius (ZMod 31) L 4)) = -4 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 31) L 4)) = 31 := by
  let z : L := algebraMap (ZMod 31) L (5 : ZMod 31)
  let n : Fin 3 := 0
  have h4 : (4 : ZMod 31) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 31) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 31) L)).mpr h4)
  have hq : Fintype.card (ZMod 31) = 6 * 5 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 31) ^ 5) ^ 2 = (5 : ZMod 31) ^ 0 := by decide
  have hy0 : ((4 : ZMod 31) ^ 5) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 31) L (parameter 1 4 5)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 31) L) hx0
  have hy : (algebraMap (ZMod 31) L (parameter 1 4 5)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 31) L) hy0
  have hF : arithmeticFrobenius (ZMod 31) L 1 = (1 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 31) L 1)) +
        (6 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = ((1 : ℕ) : ℤ) • (1 : AddMonoid.End (Points L)) +
      ((6 : ℕ) : ℤ) • rotation L
    simp only [natCast_zsmul, one_nsmul]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 31) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy 1 6 hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P31

section P43

open Paper5OrdinaryFortyThreeFrobenius

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 43) L] [CharP L 43] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_43 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 43) L 4))
      (endMap l (arithmeticFrobenius (ZMod 43) L 4)) = 8 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 43) L 4)) = 43 := by
  let z : L := algebraMap (ZMod 43) L (36 : ZMod 43)
  let n : Fin 3 := 0
  have h4 : (4 : ZMod 43) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 43) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 43) L)).mpr h4)
  have hq : Fintype.card (ZMod 43) = 6 * 7 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 43) ^ 7) ^ 2 = (36 : ZMod 43) ^ 0 := by decide
  have hy0 : ((4 : ZMod 43) ^ 7) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 43) L (parameter 1 4 7)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 43) L) hx0
  have hy : (algebraMap (ZMod 43) L (parameter 1 4 7)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 43) L) hy0
  have hF : arithmeticFrobenius (ZMod 43) L 1 = (1 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 43) L 1)) +
        (-6 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = ((1 : ℕ) : ℤ) • (1 : AddMonoid.End (Points L)) +
      Int.negSucc 5 • rotation L
    simp only [natCast_zsmul, one_nsmul, negSucc_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 43) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy 1 (-6) hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P43

section P67

open Paper5OrdinarySixtySevenFrobenius

local instance : Fact (Nat.Prime 67) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 67) L] [CharP L 67] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_67 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 67) L 4))
      (endMap l (arithmeticFrobenius (ZMod 67) L 4)) = 11 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 67) L 4)) = 67 := by
  let z : L := algebraMap (ZMod 67) L (29 : ZMod 67)
  let n : Fin 3 := 1
  have h4 : (4 : ZMod 67) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 67) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 67) L)).mpr h4)
  have hq : Fintype.card (ZMod 67) = 6 * 11 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 67) ^ 11) ^ 2 = (29 : ZMod 67) ^ 1 := by decide
  have hy0 : ((4 : ZMod 67) ^ 11) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 67) L (parameter 1 4 11)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 67) L) hx0
  have hy : (algebraMap (ZMod 67) L (parameter 1 4 11)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 67) L) hy0
  have hF : arithmeticFrobenius (ZMod 67) L 1 = (-9 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 67) L 1)) +
        (-2 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = Int.negSucc 8 • (1 : AddMonoid.End (Points L)) +
      Int.negSucc 1 • rotation L
    simp only [negSucc_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 67) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy (-9) (-2) hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P67

section P73

open Paper5OrdinarySeventyThreeFrobenius

local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 73) L] [CharP L 73] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_73 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 73) L 4))
      (endMap l (arithmeticFrobenius (ZMod 73) L 4)) = 17 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 73) L 4)) = 73 := by
  let z : L := algebraMap (ZMod 73) L (64 : ZMod 73)
  let n : Fin 3 := 2
  have h4 : (4 : ZMod 73) ≠ 0 := by decide
  have hΔ4 : (shortCubic (0 : L) (algebraMap (ZMod 73) L 4)).Δ ≠ 0 :=
    shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L)
      ((map_ne_zero (algebraMap (ZMod 73) L)).mpr h4)
  have hq : Fintype.card (ZMod 73) = 6 * 12 + 1 := by rw [ZMod.card]
  have hx0 : ((4 : ZMod 73) ^ 12) ^ 2 = (64 : ZMod 73) ^ 2 := by decide
  have hy0 : ((4 : ZMod 73) ^ 12) ^ 3 = 1 := by decide
  have hx : (algebraMap (ZMod 73) L (parameter 1 4 12)) ^ 2 = z ^ n.val := by
    simpa only [z, n, parameter, div_one, map_pow] using congrArg (algebraMap (ZMod 73) L) hx0
  have hy : (algebraMap (ZMod 73) L (parameter 1 4 12)) ^ 3 = 1 := by
    simpa only [parameter, div_one, map_pow, map_one] using congrArg (algebraMap (ZMod 73) L) hy0
  have hF : arithmeticFrobenius (ZMod 73) L 1 = (-1 : ℤ) •
      (1 : AddMonoid.End (Geometric (ZMod 73) L 1)) +
        (8 : ℤ) • CubicCubeRotation.rotate z (cube_rotation L) (discriminant_ne_zero L) := by
    change nativeFrobenius L = Int.negSucc 0 • (1 : AddMonoid.End (Points L)) +
      ((8 : ℕ) : ℤ) • rotation L
    simp only [negSucc_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  have h := CubicOrdinatePreservingTate.trace_det (two_ne_zero L) (three_ne_zero L)
    (1 : ZMod 73) 4 one_ne_zero h4 hq (discriminant_ne_zero L) hΔ4 z (cube_rotation L)
    (rotation_ne_one L) n hx hy (-1) 8 hF l hl
  norm_num [rotatedCoefficients, n] at h
  exact h

end P73

end
end ManuscriptAudit.Paper5LaterMidSplitTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterMidSplitTate.trace_det_31,
      ``ManuscriptAudit.Paper5LaterMidSplitTate.trace_det_43,
      ``ManuscriptAudit.Paper5LaterMidSplitTate.trace_det_67,
      ``ManuscriptAudit.Paper5LaterMidSplitTate.trace_det_73] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
