import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationTateRankTwo
import PrimalitySheafVerification.ManuscriptAudit.RankTwoQuadraticOperator

/-! The exact trace and norm of integral rotation coefficients on the geometric Tate modules. -/

namespace ManuscriptAudit.CubicTateRotationCoefficients

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open Module PowerTateModule RankTwoQuadraticOperator

noncomputable section

section Linear

variable {R V : Type*} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]

/-- The trace and determinant of a scalar plus a cube rotation on a free rank-two module. -/
theorem trace_det_linear (B : Basis (Fin 2) R V) (S : Module.End R V)
    (hN : ¬∃ c : R, S = c • (1 : Module.End R V)) (hS : S ^ 2 + S + 1 = 0) (a b : R) :
    LinearMap.trace R V (a • (1 : Module.End R V) + b • S) = 2 * a - b ∧
      LinearMap.det (a • (1 : Module.End R V) + b • S) = a ^ 2 - a * b + b ^ 2 := by
  let I : Module.End R V := 1
  have hQ : S ^ 2 - (-1 : R) • S + (1 : R) • I = 0 := by
    rw [neg_one_smul, one_smul, sub_neg_eq_add]
    exact hS
  obtain ⟨ht, hd⟩ := trace_det_of_quadratic B S hN (-1) 1 hQ
  let M := LinearMap.toMatrix B B S
  have hM : LinearMap.toMatrix B B (a • I + b • S) = a • (1 : Matrix (Fin 2) (Fin 2) R) + b • M := by
    simp only [M, I, map_add, map_smul, LinearMap.toMatrix_one]
  have hMt : M 0 0 + M 1 1 = -1 := by
    rw [← Matrix.trace_fin_two]
    change Matrix.trace (LinearMap.toMatrix B B S) = -1
    rw [← LinearMap.trace_eq_matrix_trace R B]
    exact ht
  have hMd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    change Matrix.det (LinearMap.toMatrix B B S) = 1
    rw [LinearMap.det_toMatrix B]
    exact hd
  constructor
  · calc
      LinearMap.trace R V (a • I + b • S) = (a + b * M 0 0) + (a + b * M 1 1) := by
        rw [LinearMap.trace_eq_matrix_trace R B, hM, Matrix.trace_fin_two]
        simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      _ = 2 * a + b * (M 0 0 + M 1 1) := by ring
      _ = 2 * a - b := by rw [hMt]; ring
  · calc
      LinearMap.det (a • I + b • S) =
          (a + b * M 0 0) * (a + b * M 1 1) - (b * M 0 1) * (b * M 1 0) := by
        rw [← LinearMap.det_toMatrix B, hM, Matrix.det_fin_two]
        simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      _ = a ^ 2 + a * b * (M 0 0 + M 1 1) + b ^ 2 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by ring
      _ = a ^ 2 - a * b + b ^ 2 := by rw [hMt, hMd]; ring

end Linear

private def rotationCombination {G : Type*} [AddCommGroup G] (r : AddMonoid.End G) (a b : ℤ) :
    AddMonoid.End G := a • (1 : AddMonoid.End G) + b • r

variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {A z : L}

/-- Integral point-group rotation coefficients give exact coefficients on both geometric Tate modules. -/
theorem trace_det (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (hΔ : (shortCubic (0 : L) A).Δ ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3)
    (F : AddMonoid.End (Curve A).Point) (a b : ℤ)
    (hF : F = rotationCombination (CubicCubeRotation.rotate z hz hΔ) a b) :
    LinearMap.trace ℤ_[l] (Tate l (Curve A).Point) (endMap l F) = ((2 * a - b : ℤ) : ℤ_[l]) ∧
      LinearMap.det (endMap l F) = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℤ_[l]) := by
  let B := CubicRotationTateRankTwo.tateBasis h₂ h₃ hA hz hz₁ l hl
  let r : AddMonoid.End (Curve A).Point := CubicCubeRotation.rotate z hz hΔ
  let S := endMap l r
  have hN : ¬∃ c : ℤ_[l], S = c • (1 : Module.End ℤ_[l] (Tate l (Curve A).Point)) :=
    CubicRotationTateRankTwo.rotation_not_scalar h₂ h₃ hA hz hz₁ l hl
  have hr : r ^ 2 + r + (1 : AddMonoid.End (Curve A).Point) = 0 := by
    apply AddMonoidHom.ext
    intro P
    change r (r P) + r P + P = 0
    exact CubicRotationQuadratic.rotate_sum_eq_zero h₂ h₃ hA hz hz₁ hΔ P
  have hS : S ^ 2 + S + 1 = 0 := by
    simpa only [S, map_add, map_pow, map_one, map_zero] using congrArg (endMap l) hr
  have hF' : endMap l F = (a : ℤ_[l]) • 1 + (b : ℤ_[l]) • S := by
    let I : AddMonoid.End (Curve A).Point := 1
    let J : Module.End ℤ_[l] (Tate l (Curve A).Point) := 1
    have hFa : (endMap l) (a • I) = (a : ℤ_[l]) • J := by
      calc
        _ = a • (endMap l) I := map_zsmul (endMap l) I a
        _ = a • J := congrArg (fun f : Module.End ℤ_[l] (Tate l (Curve A).Point) => a • f)
          (map_one (endMap l))
        _ = _ := (Int.cast_smul_eq_zsmul ℤ_[l] a J).symm
    have hFb : (endMap l) (b • r) = (b : ℤ_[l]) • S :=
      (map_zsmul (endMap l) r b).trans (Int.cast_smul_eq_zsmul ℤ_[l] b S).symm
    have he := congrArg (endMap l) hF
    change (endMap l) F = (endMap l) (a • I + b • r) at he
    exact he.trans ((map_add (endMap l) (a • I) (b • r)).trans (congrArg₂ (· + ·) hFa hFb))
  rw [hF']
  simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using
    trace_det_linear B S hN hS (a : ℤ_[l]) (b : ℤ_[l])

end
end ManuscriptAudit.CubicTateRotationCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTateRotationCoefficients.trace_det_linear,
      ``ManuscriptAudit.CubicTateRotationCoefficients.trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
