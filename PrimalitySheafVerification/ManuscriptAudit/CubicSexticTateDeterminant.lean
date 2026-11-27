import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticRotation
import PrimalitySheafVerification.ManuscriptAudit.PadicNoPrimitiveCube
import PrimalitySheafVerification.ManuscriptAudit.RankTwoCoefficientIdentification
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! Genuine sixth-root scaling has determinant one on a rank-two 2-adic or 3-adic Tate module. -/

namespace ManuscriptAudit.CubicSexticTateDeterminant

open Module FiniteFieldPointCount CubicCubeRotation CubicRotationQuadratic PowerTateModule
open CubicSupersingularUnitFrobenius CubicSupersingularTwistFrobenius CubicSexticRotation
open scoped Padic

noncomputable section

variable (L : Type*) [Field L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

/-- Every actual sixth-root twist correction has determinant one, independently of characteristic. -/
theorem det_sexticScale (hl : l = 2 ∨ l = 3) (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0)
    (B : Basis (Fin 2) ℤ_[l] (Tate l (UnitPoints L)))
    (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) {v : L} (hv : v ^ 6 = 1) :
    LinearMap.det (endMap l (sexticScale L hv hΔ)) = 1 := by
  let U := Tate l (UnitPoints L)
  let r : AddMonoid.End (UnitPoints L) := rotate (v ^ 2) (square_cube L hv) hΔ
  let R := endMap l r
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  have hRank : finrank ℤ_[l] U = 2 := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  have hR : LinearMap.det R = 1 := by
    by_cases h : v ^ 2 = 1
    · have hr : r = 1 := rotate_eq_id L hΔ (square_cube L hv) h
      simp [R, hr]
    · have hr : r ^ 2 + r + 1 = 0 := by
        apply AddMonoidHom.ext
        intro P
        change r (r P) + r P + P = 0
        exact rotate_sum_eq_zero h₂ h₃ one_ne_zero (square_cube L hv) h hΔ P
      have ht := congrArg (endMap l) hr
      have hQuad : R ^ 2 - (-1 : ℤ_[l]) • R + (1 : ℤ_[l]) • (1 : Module.End ℤ_[l] U) = 0 := by
        rw [show ((-1 : ℤ_[l]) • R) = -R from neg_one_smul ℤ_[l] R, sub_neg_eq_add, one_smul]
        simpa only [R, map_pow, map_add, map_one, map_zero] using ht
      have hNo (u : ℤ_[l]) : u ^ 2 - (-1 : ℤ_[l]) * u + 1 ≠ 0 := by
        intro hEq
        have he := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) hEq
        push_cast at he
        exact PadicNoPrimitiveCube.no_root l hl (u : ℚ_[l])
          (by simpa only [neg_one_mul, sub_neg_eq_add] using he)
      exact (RankTwoCoefficientIdentification.linear_trace_det B R (-1) 1 hNo hQuad).2
  have hs : endMap l (sexticScale L hv hΔ) = ((twistSign L v : ℤ) : ℤ_[l]) • R := by
    have hMap : endMap l (twistSign L v • r) = twistSign L v • R :=
      (endMap l : AddMonoid.End (UnitPoints L) →+* Module.End ℤ_[l] U).toAddMonoidHom.map_zsmul
        (twistSign L v) r
    rw [CubicSexticRotation.sextic_eq_signed_rotation, Int.cast_smul_eq_zsmul]
    exact hMap
  have hSign : ((twistSign L v : ℤ) : ℤ_[l]) ^ 2 = 1 := by
    rcases twistSign_cases L v with h | h <;> simp [h]
  rw [hs, LinearMap.det_smul, hRank, hSign, hR, one_mul]

end

end ManuscriptAudit.CubicSexticTateDeterminant

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSexticTateDeterminant.det_sexticScale
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
