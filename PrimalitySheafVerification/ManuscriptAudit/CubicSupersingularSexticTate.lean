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

theorem trace_det (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0)
    (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) {v : L} (hv : v ^ 6 = 1) :
    let S := endMap l (sexticScale L hv hΔ)
    ∃ t : ℤ, (t = 2 ∨ t = -2 ∨ t = 1 ∨ t = -1) ∧
      LinearMap.trace ℤ_[l] (Tate l (UnitPoints L)) S = (t : ℤ_[l]) ∧ LinearMap.det S = 1 := by
  let B := CubicNonsplitFiniteFieldTate.centeredBasis p L l hp hp₃ hlp one_ne_zero hΔ
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let U := Tate l (UnitPoints L)
  let R := endMap l (rotate (v ^ 2) (square_cube L hv) hΔ)
  have hRank : finrank ℤ_[l] U = 2 := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  have hD : ∃ t : ℤ, (t = 2 ∨ t = -1) ∧
      LinearMap.trace ℤ_[l] U R = (t : ℤ_[l]) ∧ LinearMap.det R = 1 := by
    by_cases h : v ^ 2 = 1
    · have hR : R = 1 := by
        have he : rotate (v ^ 2) (square_cube L hv) hΔ = 1 := by
          simpa only [h] using rotate_one L hΔ
        simp only [R, he, map_one]
      refine ⟨2, Or.inl rfl, ?_, ?_⟩
      · rw [hR, LinearMap.trace_one, hRank] <;> rfl
      · simp [hR]
    · obtain ⟨ht, hd⟩ := CubicSupersingularRotationTate.trace_det
        p L l hp hp₃ hlp h₂ h₃ hΔ (square_cube L hv) h
      exact ⟨-1, Or.inr rfl, by simpa using ht, hd⟩
  obtain ⟨t, hT, ht, hd⟩ := hD
  rcases cube_sign L hv with h | h
  · have hS : endMap l (sexticScale L hv hΔ) = R :=
      congrArg (endMap l) (sextic_eq_rotation L hv hΔ h)
    rw [hS]
    refine ⟨t, ?_, ht, hd⟩
    rcases hT with rfl | rfl <;> simp
  · have hS : endMap l (sexticScale L hv hΔ) = -R := by
      rw [sextic_eq_neg_rotation L hv hΔ h, map_neg]
    rw [hS]
    refine ⟨-t, ?_, ?_, ?_⟩
    · rcases hT with rfl | rfl <;> simp
    · rw [map_neg, ht, Int.cast_neg]
    · rw [← neg_one_smul (ℤ_[l]) R, LinearMap.det_smul, hRank, hd]
      norm_num

end
end ManuscriptAudit.CubicSupersingularSexticTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularSexticTate.trace_det
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
