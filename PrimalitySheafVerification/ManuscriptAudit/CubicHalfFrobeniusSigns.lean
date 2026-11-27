import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusScaling
import PrimalitySheafVerification.ManuscriptAudit.CubicExplicitHalfTorsion

/-! Finite-field Frobenius signs for square-root coordinates of native two-torsion halves. -/

namespace ManuscriptAudit.CubicHalfFrobeniusSigns

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicExplicitHalfTorsion CubicFrobeniusScaling

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K] [Field L] [Algebra K L]

/-- A geometric square root of a base scalar acquires its base quadratic-character sign. -/
theorem frobenius_sqrt (hchar : ringChar K ≠ 2) {d : K} {r : L}
    (hr : r ^ 2 = algebraMap K L d) :
    r ^ Fintype.card K = algebraMap K L (quadraticChar K d : K) * r := by
  have hOdd := FiniteField.odd_card_of_char_ne_two hchar
  have hq : Fintype.card K = 2 * (Fintype.card K / 2) + 1 := by omega
  calc
    _ = r ^ (2 * (Fintype.card K / 2) + 1) := congrArg (fun n : ℕ => r ^ n) hq
    _ = _ := by
      rw [pow_succ, pow_mul, hr, ← map_pow,
        ← quadraticChar_eq_pow_of_char_ne_two' hchar d]

/-- In a field of size three modulo four, the two differences from a primitive
cube root and its conjugate have opposite quadratic characters. -/
theorem difference_signs {z : K} (hz : IsPrimitiveRoot z 3)
    (hq : Fintype.card K % 4 = 3) :
    quadraticChar K (z ^ 2 - 1) = -quadraticChar K (z - 1) := by
  have hnot : ¬ IsSquare (-1 : K) := fun h =>
    (FiniteField.isSquare_neg_one_iff.mp h) hq
  have hχ : quadraticChar K (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hnot
  have hSquare : quadraticChar K (z ^ 2) = 1 := quadraticChar_sq_one' (hz.ne_zero (by decide))
  have hFactor : z ^ 2 - 1 = ((-1 : K) * z ^ 2) * (z - 1) := by
    calc
      _ = z ^ 2 - z ^ 3 := by rw [hz.pow_eq_one]
      _ = _ := by ring
  rw [hFactor, map_mul, map_mul, hχ, hSquare, mul_one, neg_one_mul]

variable [DecidableEq L]

/-- Transport the exact half coordinates through the actual native point map. -/
theorem native_map_half (g : L →ₐ[K] L) (A : K) {a r s r' s' : L}
    (hΔ : (shortCubic (0 : L) (algebraMap K L A)).Δ ≠ 0)
    (ha : a ^ 3 + algebraMap K L A = 0) (haFix : g a = a)
    (hSum : r ^ 2 + s ^ 2 = 3 * a) (hProd : (r * s) ^ 2 = 3 * a ^ 2)
    (hSum' : r' ^ 2 + s' ^ 2 = 3 * a) (hProd' : (r' * s') ^ 2 = 3 * a ^ 2)
    (hr : g r = r') (hs : g s = s') :
    nativeMap K L g A (halfPoint hΔ ha hSum hProd) =
      halfPoint hΔ ha hSum' hProd' := by
  unfold halfPoint
  obtain ⟨_, h⟩ := nativeMap_some K L g A
    ((nonsingular_iff hΔ _ _).mpr (half_equation ha hSum hProd))
  rw [h, Affine.Point.some.injEq]
  constructor
  · simp [halfX, haFix, hr, hs]
  · simp [halfY, hr, hs]

end
end ManuscriptAudit.CubicHalfFrobeniusSigns

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicHalfFrobeniusSigns.frobenius_sqrt,
      ``ManuscriptAudit.CubicHalfFrobeniusSigns.difference_signs,
      ``ManuscriptAudit.CubicHalfFrobeniusSigns.native_map_half] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
