import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualLocalZetaPoles

/-! The rational continuation of the actual local zeta has its two roots on the Hasse circle. -/

namespace ManuscriptAudit.Paper5ActualLocalZetaZeros

open Paper5ActualHasseWeil Paper5AnalyticEuler Paper5ActualAnalyticLocalZeta
open Paper5ActualLocalZetaPoles

noncomputable section

theorem actual_local_zeros (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    ∃ α β : ℂ,
      ‖α‖ = Real.sqrt p ∧ ‖β‖ = Real.sqrt p ∧
      α⁻¹ ∈ awayFromPoles (p : ℂ) ∧ β⁻¹ ∈ awayFromPoles (p : ℂ) ∧
      ∀ z ∈ awayFromPoles (p : ℂ),
        rationalZeta (p : ℂ) (firstTrace p A : ℂ) z = 0 ↔ z = α⁻¹ ∨ z = β⁻¹ := by
  obtain ⟨α, β, hsum, hmul, hα, hβ⟩ := exists_actual_roots hp hA
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have h₀ : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs₀ := Real.sqrt_nonneg (p : ℝ)
  have hs₂ := Real.sq_sqrt hpR.le
  have hS₁ : 1 < Real.sqrt (p : ℝ) := by
    by_contra! h
    have hm := mul_le_mul_of_nonneg_left h hs₀
    nlinarith
  have hSp : Real.sqrt (p : ℝ) < p := by
    have hm := mul_pos (zero_lt_one.trans hS₁) (sub_pos.mpr hS₁)
    nlinarith
  have hFactor (z : ℂ) :
      1-(firstTrace p A : ℂ)*z+(p : ℂ)*z^2 = (1-α*z)*(1-β*z) := by
    linear_combination z*hsum - z^2*hmul
  have hAway (w : ℂ) (hw : ‖w‖ = Real.sqrt (p : ℝ)) :
      w⁻¹ ∈ awayFromPoles (p : ℂ) := by
    constructor
    · intro hz
      have h := congrArg (fun z : ℂ => ‖z‖) (congrArg Inv.inv hz)
      simp only [inv_inv, inv_one, norm_one, hw] at h
      linarith
    · intro hz
      have h := congrArg (fun z : ℂ => ‖z‖) (congrArg Inv.inv hz)
      simp only [inv_inv, Complex.norm_natCast, hw] at h
      linarith
  have hLinear (w z : ℂ) (hw : ‖w‖ = Real.sqrt (p : ℝ)) : 1-w*z = 0 ↔ z = w⁻¹ := by
    have hW0 : w ≠ 0 := by
      intro he
      rw [he, norm_zero] at hw
      linarith
    constructor
    · intro hh
      have hmul : w*z = 1 := (sub_eq_zero.mp hh).symm
      calc
        z = w⁻¹*(w*z) := by field_simp [hW0]
        _ = w⁻¹ := by rw [hmul, mul_one]
    · rintro rfl
      rw [mul_inv_cancel₀ hW0, sub_self]
  refine ⟨α, β, hα, hβ, hAway α hα, hAway β hβ, ?_⟩
  intro z hz
  change z ≠ 1 ∧ z ≠ (p : ℂ)⁻¹ at hz
  have hz₁ : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.1)
  have hz₂ : 1-(p : ℂ)*z ≠ 0 := by
    intro h
    apply hz.2
    have hz' : (p : ℂ)*z = 1 := (sub_eq_zero.mp h).symm
    calc
      z = (p : ℂ)⁻¹*((p : ℂ)*z) := by field_simp [h₀]
      _ = (p : ℂ)⁻¹ := by rw [hz', mul_one]
  unfold rationalZeta
  rw [hFactor, div_eq_zero_iff, or_iff_left (mul_ne_zero hz₁ hz₂), mul_eq_zero,
    hLinear α z hα, hLinear β z hβ]

theorem actual_zero_radius (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) {z : ℂ} (hz : z ∈ awayFromPoles (p : ℂ))
    (h : rationalZeta (p : ℂ) (firstTrace p A : ℂ) z = 0) :
    ‖z‖ = 1 / Real.sqrt (p : ℝ) := by
  obtain ⟨α, β, hα, hβ, _, _, hZeros⟩ := actual_local_zeros p hp hA
  rcases (hZeros z hz).mp h with rfl | rfl
  · rw [norm_inv, hα, one_div]
  · rw [norm_inv, hβ, one_div]

end
end ManuscriptAudit.Paper5ActualLocalZetaZeros

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5ActualLocalZetaZeros.actual_local_zeros,
      ``ManuscriptAudit.Paper5ActualLocalZetaZeros.actual_zero_radius] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
