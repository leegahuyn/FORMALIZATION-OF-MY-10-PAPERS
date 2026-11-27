import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticRotation
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularRotationTate

/-! Trace and determinant of the genuine geometric sixth-root scaling. -/

namespace ManuscriptAudit.CubicSupersingularSexticTate

open Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicCubeRotation PowerTateModule CubicSupersingularUnitFrobenius
open CubicSupersingularTwistFrobenius CubicSexticRotation

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

/-- The actual signed rotation has its exact trace factor, independent of the coefficient prime. -/
theorem trace_det_formula (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0)
    (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) {v : L} (hv : v ^ 6 = 1) :
    let S := endMap l (sexticScale L hv hΔ)
    let t := twistSign L v * (if v ^ 2 = 1 then (2 : ℤ) else -1)
    LinearMap.trace ℤ_[l] (Tate l (UnitPoints L)) S = (Int.cast t : ℤ_[l]) ∧ LinearMap.det S = 1 := by
  let B := CubicNonsplitFiniteFieldTate.centeredBasis p L l hp hp₃ hlp one_ne_zero hΔ
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let U := Tate l (UnitPoints L)
  let r : AddMonoid.End (UnitPoints L) := rotate (v ^ 2) (square_cube L hv) hΔ
  let R := endMap l r
  let a : ℤ_[l] := Int.cast (twistSign L v)
  let k : ℤ := if v ^ 2 = 1 then 2 else -1
  have hRank : finrank ℤ_[l] U = 2 := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  have hR : LinearMap.trace ℤ_[l] U R = (Int.cast k : ℤ_[l]) ∧ LinearMap.det R = 1 := by
    by_cases h : v ^ 2 = 1
    · have he : r = 1 := rotate_eq_id L hΔ (square_cube L hv) h
      refine ⟨?_, ?_⟩
      · simp [R, he, hRank, k, h]
      · simp [R, he]
    · obtain ⟨ht, hd⟩ := CubicSupersingularRotationTate.trace_det
        p L l hp hp₃ hlp h₂ h₃ hΔ (square_cube L hv) h
      exact ⟨by simpa [k, h] using ht, hd⟩
  have hS : endMap l (sexticScale L hv hΔ) = a • R := by
    calc
      _ = twistSign L v • R :=
        (congrArg (endMap l) (sextic_eq_signed_rotation L hv hΔ)).trans
          (map_zsmul (endMap l) r (twistSign L v))
      _ = _ := (Int.cast_smul_eq_zsmul ℤ_[l] (twistSign L v) R).symm
  have hA : a ^ 2 = 1 := by
    rcases twistSign_cases L v with h | h <;> simp [a, h]
  change LinearMap.trace ℤ_[l] U (endMap l (sexticScale L hv hΔ)) =
    (Int.cast (twistSign L v * k) : ℤ_[l]) ∧ LinearMap.det (endMap l (sexticScale L hv hΔ)) = 1
  rw [hS]
  constructor
  · rw [map_smul, hR.1, smul_eq_mul, Int.cast_mul]
  · rw [LinearMap.det_smul, hRank, hA, hR.2, one_mul]

theorem trace_det (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0)
    (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) {v : L} (hv : v ^ 6 = 1) :
    let S := endMap l (sexticScale L hv hΔ)
    ∃ t : ℤ, (t = 2 ∨ t = -2 ∨ t = 1 ∨ t = -1) ∧
      LinearMap.trace ℤ_[l] (Tate l (UnitPoints L)) S = (t : ℤ_[l]) ∧ LinearMap.det S = 1 := by
  let t := twistSign L v * (if v ^ 2 = 1 then (2 : ℤ) else -1)
  obtain ⟨ht, hd⟩ := trace_det_formula p L l hp hp₃ hlp h₂ h₃ hΔ hv
  refine ⟨t, ?_, ht, hd⟩
  by_cases h : v ^ 2 = 1 <;>
    rcases twistSign_cases L v with h₁ | h₁ <;> simp [t, h, h₁]

end
end ManuscriptAudit.CubicSupersingularSexticTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSupersingularSexticTate.trace_det_formula,
      ``ManuscriptAudit.CubicSupersingularSexticTate.trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
