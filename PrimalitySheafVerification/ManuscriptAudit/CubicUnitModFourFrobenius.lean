import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.CubicUnitHalfFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationBasisFromHalf
import PrimalitySheafVerification.ManuscriptAudit.CubicRotatedModFourTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitFrobeniusModFourPatterns

/-! The signed actual reference Frobenius operator on geometric four-torsion. -/

namespace ManuscriptAudit.CubicUnitModFourFrobenius

open Module CubicUnitHalfFrobenius CubicRotationBasisFromHalf CubicRotatedModFourTrace
open CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius TorsionFrobeniusModule

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K L]

/-- The actual reference operator is `χ(ζ−1) I + 2 ρ` on four-torsion. -/
theorem operator_eq_signed_rotation {z : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hz : IsPrimitiveRoot z 3)
    (hq : Fintype.card K % 4 = 3) :
    let S := levelRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz 2
    levelFrobenius K L (1 : K) 2 = (quadraticChar K (z - 1) : ZMod 4) • 1 + (2 : ZMod 4) • S := by
  let f := arithmeticPointFrobenius K L (1 : K)
  let r := geometricRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz
  let F := levelFrobenius K L (1 : K) 2
  let S := levelRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz 2
  let σ : ZMod 4 := quadraticChar K (z - 1)
  let M : Module.End (ZMod 4) (Level K L (1 : K) 2) := σ • 1 + (2 : ZMod 4) • S
  obtain ⟨T, P, hT, hDist, hT₂, hDouble, hFP⟩ := exists_half_frobenius K L h₂ h₃ hz hq
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L (1 : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr one_ne_zero
  have hzL := hz.map_of_injective (algebraMap K L).injective
  obtain ⟨B, hB₀, hB₁⟩ := exists_basis_from_half h₂L h₃L hAL hzL.pow_eq_one T P
    hT hT₂ hDouble hDist
  have hB : S (B 0) = B 1 := hB₁
  have h₀ : F (B 0) = M (B 0) := by
    change F (B 0) = ((quadraticChar K (z - 1) : ℤ) : ZMod 4) • B 0 +
      ((2 : ℕ) : ZMod 4) • S (B 0)
    rw [Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul]
    apply Subtype.ext
    change f (B 0).val = quadraticChar K (z - 1) • (B 0).val + (2 : ℕ) • r (B 0).val
    rw [hB₀, ← map_nsmul, hDouble]
    exact hFP
  have hComm : F (S (B 0)) = S (F (B 0)) := congrArg
    (fun m : Module.End (ZMod 4) (Level K L (1 : K) 2) => m (B 0))
    (level_commutes K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz 2)
  have h₁ : F (B 1) = M (B 1) := by
    rw [← hB, hComm, h₀]
    change S (σ • B 0 + (2 : ZMod 4) • S (B 0)) =
      σ • S (B 0) + (2 : ZMod 4) • S (S (B 0))
    rw [map_add, map_smul, map_smul]
  change F = M
  apply B.ext
  intro j
  fin_cases j
  · exact h₀
  · exact h₁

/-- The two actual cubic rotations of the reference Frobenius have opposite signed traces. -/
theorem rotated_trace {z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hz : IsPrimitiveRoot z 3) (hq : Fintype.card K % 4 = 3) :
    let S := levelRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz 2
    let F := levelFrobenius K L (1 : K) 2
    LinearMap.trace (ZMod 4) (Level K L (1 : K) 2) (S * F) = (quadraticChar K (z - 1) : ZMod 4) ∧
      LinearMap.trace (ZMod 4) (Level K L (1 : K) 2) (S ^ 2 * F) = -(quadraticChar K (z - 1) : ZMod 4) := by
  let S := levelRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz 2
  let σ : ZMod 4 := quadraticChar K (z - 1)
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L (1 : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr one_ne_zero
  have hzL := hz.map_of_injective (algebraMap K L).injective
  have hSq : S ^ 2 = -S - 1 := by
    apply LinearMap.ext
    intro P
    change S (S P) = -S P - P
    have h : S (S P) = -P - S P :=
      CubicRotationCyclicBasis.rotation_linear_quad h₂L h₃L hAL
        hzL.pow_eq_one (hzL.ne_one (by decide)) 2 P
    rw [h]
    abel
  have hσ : σ = 1 ∨ σ = -1 := by
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr (hz.ne_one (by decide))) with h | h
    · exact Or.inl (by simp only [σ, h, Int.cast_one])
    · exact Or.inr (by simp only [σ, h, Int.cast_neg, Int.cast_one])
  obtain ⟨B, h₀, h₁, _, _, _⟩ :=
    CubicSplitFrobeniusModFourPatterns.exists_native_rotation_form K L h₂ h₃
      (one_ne_zero : (1 : K) ≠ 0) hz
  dsimp only
  rw [operator_eq_signed_rotation K L h₂ h₃ hz hq]
  exact traces_of_two_rotations B S h₀ h₁ hSq σ hσ

end
end ManuscriptAudit.CubicUnitModFourFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicUnitModFourFrobenius.operator_eq_signed_rotation,
      ``ManuscriptAudit.CubicUnitModFourFrobenius.rotated_trace] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
