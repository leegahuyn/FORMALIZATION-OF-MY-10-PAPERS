import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTwistParameters

/-! The traces and determinants of the three rotations of the native reference Frobenius. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenRotatedTate

open Module Paper5OrdinaryNineteenCoordinates Paper5OrdinaryNineteenFrobenius
open Paper5OrdinaryNineteenAlgebra
open Paper5OrdinaryNineteenTwistParameters PowerTateModule RankTwoQuadraticOperator

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

abbrev rotationAction : Module.End ℤ_[l] (Tate l (Points L)) := endMap l (rotation L)

abbrev rotatedAction (j : Fin 3) : Module.End ℤ_[l] (Tate l (Points L)) :=
  rotationAction L l ^ j.val * Paper5OrdinaryNineteenTate.action L l

private theorem point_rotation_quadratic :
    rotation L ^ 2 + rotation L + (1 : AddMonoid.End (Points L)) = 0 := by
  apply AddMonoidHom.ext
  intro P
  change rotation L (rotation L P) + rotation L P + P = 0
  rw [rotation_sq]
  abel

private theorem rotate_frobenius :
    rotation L * nativeFrobenius L = -((2 : ℕ) • 1) + (3 : ℕ) • rotation L := by
  apply AddMonoidHom.ext
  intro P
  change rotation L (nativeFrobenius L P) = -((2 : ℕ) • P) + (3 : ℕ) • rotation L P
  have h := congrArg (fun f : AddMonoid.End (Points L) => f P) (native_eq_rotation L)
  change nativeFrobenius L P = (5 : ℕ) • P + (2 : ℕ) • rotation L P at h
  rw [h]
  simp only [map_add, map_nsmul, rotation_sq]
  abel

private theorem rotate_twice_frobenius :
    rotation L ^ 2 * nativeFrobenius L = -((3 : ℕ) • 1) - (5 : ℕ) • rotation L := by
  apply AddMonoidHom.ext
  intro P
  rw [pow_two]
  change rotation L ((rotation L * nativeFrobenius L) P) = -((3 : ℕ) • P) - (5 : ℕ) • rotation L P
  rw [rotate_frobenius]
  change rotation L (-((2 : ℕ) • P) + (3 : ℕ) • rotation L P) = _
  simp only [map_add, map_neg, map_nsmul, rotation_sq]
  abel

theorem rotation_trace_det (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (rotationAction L l) = -1 ∧
      LinearMap.det (rotationAction L l) = 1 := by
  let S := rotationAction L l
  have hn : ¬∃ c : ℤ_[l], S = c • (1 : Module.End ℤ_[l] (Tate l (Points L))) :=
    CubicRotationTateRankTwo.rotation_not_scalar (A := (1 : L)) (z := (7 : L))
      (numeral_ne_zero 2 (by decide)) (numeral_ne_zero 3 (by decide))
      one_ne_zero rotation_cube rotation_ne_one l hl
  have hq : S ^ 2 - (-1 : ℤ_[l]) • S + (1 : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (Points L))) = 0 := by
    have hnS : (-1 : ℤ_[l]) • S = -S := neg_one_smul (ℤ_[l]) S
    rw [hnS, one_smul]
    calc
      _ = S ^ 2 + S + 1 := by abel
      _ = 0 := by
        simpa only [map_add, map_pow, map_one, map_zero] using
          congrArg (endMap l) (point_rotation_quadratic L)
  exact trace_det_of_quadratic (Paper5OrdinaryNineteenTate.tateBasis L l hl) S hn (-1) 1 hq

/-- Every rotated reference Frobenius has determinant nineteen and the tabled trace. -/
theorem trace_det (hl : l = 2 ∨ l = 3) (j : Fin 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (rotatedAction L l j) = (rotatedTrace j : ℤ_[l]) ∧
      LinearMap.det (rotatedAction L l j) = 19 := by
  let B := Paper5OrdinaryNineteenTate.tateBasis L l hl
  let S := rotationAction L l
  let F := Paper5OrdinaryNineteenTate.action L l
  let I : Module.End ℤ_[l] (Tate l (Points L)) := 1
  obtain ⟨hSt, hSd⟩ := rotation_trace_det L l hl
  obtain ⟨hFt, hFd⟩ := Paper5OrdinaryNineteenTate.trace_det L l hl
  have hIt : LinearMap.trace ℤ_[l] (Tate l (Points L)) I = 2 := by
    simp [I, LinearMap.trace_eq_matrix_trace ℤ_[l] B]
  have h₁ : S * F = -((2 : ℤ_[l]) • I) + (3 : ℤ_[l]) • S := by
    change _ = -(((2 : ℕ) : ℤ_[l]) • I) + ((3 : ℕ) : ℤ_[l]) • S
    simpa only [Nat.cast_smul_eq_nsmul, map_mul, map_add, map_neg, map_nsmul, map_one] using
      congrArg (endMap l) (rotate_frobenius L)
  have h₂ : S ^ 2 * F = -((3 : ℤ_[l]) • I) - (5 : ℤ_[l]) • S := by
    change _ = -(((3 : ℕ) : ℤ_[l]) • I) - ((5 : ℕ) : ℤ_[l]) • S
    simpa only [Nat.cast_smul_eq_nsmul, map_mul, map_pow, map_sub, map_neg, map_nsmul, map_one] using
      congrArg (endMap l) (rotate_twice_frobenius L)
  have ht₁ : LinearMap.trace ℤ_[l] (Tate l (Points L)) (S * F) = -7 := by
    rw [h₁]
    simp only [map_add, map_neg, map_smul, hIt, hSt, smul_eq_mul]
    norm_num
  have ht₂ : LinearMap.trace ℤ_[l] (Tate l (Points L)) (S ^ 2 * F) = -1 := by
    rw [h₂]
    simp only [map_sub, map_neg, map_smul, hIt, hSt, smul_eq_mul]
    norm_num
  constructor
  · fin_cases j
    · simpa [rotatedAction, rotatedTrace, F, S] using hFt
    · simpa [rotatedAction, rotatedTrace, F, S] using ht₁
    · simpa [rotatedAction, rotatedTrace, F, S] using ht₂
  · simp only [rotatedAction, map_mul, map_pow, hSd, hFd, one_pow, one_mul]

end
end ManuscriptAudit.Paper5OrdinaryNineteenRotatedTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenRotatedTate.rotation_trace_det,
      ``ManuscriptAudit.Paper5OrdinaryNineteenRotatedTate.trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
