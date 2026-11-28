import Lean.Util.CollectAxioms
import Mathlib.Analysis.RCLike.Sqrt
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaDedekindTranslation
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaDedekindInversion

/-! A Euclidean step for every positive lower-left entry beyond the arithmetic base case. -/

namespace ManuscriptAudit.Paper8EtaMultiplierEuclideanStep

open Paper8EtaPositiveLowerLeftMultiplier Paper8EtaDedekindTranslation Paper8EtaDedekindInversion
open scoped MatrixGroups

private theorem determinant_equation (g : SL(2, ℤ)) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  change Matrix.det g.1 = (1 : ℤ) at h
  rwa [Matrix.det_fin_two] at h

private theorem lowerRight_emod_pos {g : SL(2, ℤ)} (hc : 0 < g 1 0) (hOne : g 1 0 ≠ 1) :
    0 < g 1 1 % g 1 0 := by
  have hNonneg : 0 ≤ g 1 1 % g 1 0 := Int.emod_nonneg _ hc.ne'
  by_contra! hZero
  have hR : g 1 1 % g 1 0 = 0 := le_antisymm hZero hNonneg
  have hDiv := Int.emod_add_mul_ediv (g 1 1) (g 1 0)
  rw [hR, zero_add] at hDiv
  let q := g 0 0 * (g 1 1 / g 1 0) - g 0 1
  have hQ : g 1 0 * q = 1 := by
    unfold q
    calc
      _ = g 0 0 * (g 1 0 * (g 1 1 / g 1 0)) - g 0 1 * g 1 0 := by ring
      _ = _ := by rw [hDiv]; exact determinant_equation g
  have hQPos : 0 < q := by
    by_contra! h
    have hP := mul_nonpos_of_nonneg_of_nonpos hc.le h
    omega
  have hQL : 1 ≤ q := by omega
  have hBound : g 1 0 ≤ g 1 0 * q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQL hc.le
  omega

theorem principalEtaMultiplier_euclidean_step (g : SL(2, ℤ)) (hc : 0 < g 1 0) :
    g 1 0 = 1 ∨ ∃ m : ℤ,
      let g' := (g * ModularGroup.T ^ m) * ModularGroup.S
      0 < g' 1 0 ∧ g' 1 0 < g 1 0 ∧
        principalEtaMultiplier g =
          (Complex.sqrt Complex.I / translationPhase m) * principalEtaMultiplier g' := by
  by_cases hOne : g 1 0 = 1
  · exact Or.inl hOne
  · right
    let m : ℤ := -(g 1 1 / g 1 0)
    let h := g * ModularGroup.T ^ m
    let g' := h * ModularGroup.S
    have hTc : h 1 0 = g 1 0 := (right_T_entries g m).2.1
    have hTd : h 1 1 = g 1 1 % g 1 0 := by
      change (g * ModularGroup.T ^ m) 1 1 = _
      rw [(right_T_entries g m).2.2]
      unfold m
      have hDiv := Int.emod_add_mul_ediv (g 1 1) (g 1 0)
      rw [mul_neg]
      linarith
    have hSc : g' 1 0 = h 1 1 := (right_S_entries h).1
    have hPos : 0 < h 1 1 := by rw [hTd]; exact lowerRight_emod_pos hc hOne
    have hLt : h 1 1 < g 1 0 := by rw [hTd]; exact Int.emod_lt_of_pos _ hc
    have hPosC : 0 < h 1 0 := by rwa [hTc]
    have hInv := principalEtaMultiplier_mul_S h hPosC hPos
    change principalEtaMultiplier g' = principalEtaMultiplier (g * ModularGroup.T ^ m) /
      Complex.sqrt Complex.I at hInv
    rw [principalEtaMultiplier_mul_T g hc m] at hInv
    refine ⟨m, ?_⟩
    change 0 < g' 1 0 ∧ g' 1 0 < g 1 0 ∧ _
    refine ⟨by rwa [hSc], by rwa [hSc], ?_⟩
    have hI : Complex.sqrt Complex.I ≠ 0 := by
      rw [sqrt_eq_exp Complex.I_ne_zero]
      exact Complex.exp_ne_zero _
    have hE : translationPhase m ≠ 0 := Complex.exp_ne_zero _
    rw [hInv]
    field_simp [hI, hE] <;> ring

end ManuscriptAudit.Paper8EtaMultiplierEuclideanStep

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EtaMultiplierEuclideanStep.principalEtaMultiplier_euclidean_step
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
