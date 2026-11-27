import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8XiFactorization
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadowPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadowNonzero

/-!
# The two printed ξ conventions cannot be related by a shadow rescaling

Physical p. 334 uses the un-conjugated differential. Physical p. 336
uses the conjugated differential. On the actual p. 338 unary shadow
the two outputs have conjugate and distinct translation phases.
-/

namespace ManuscriptAudit.Paper8XiShadowConventions

open MaassLaplacian (complexPoint)
open Paper8XiShadow (Field)
open Paper8XiFactorization (conjugatedXi unconjugatedXi conjugatedXi_eq_literal
  unconjugatedXi_eq_literal)
open Paper8KroneckerShadow (unaryShadow)
open Paper8KroneckerShadowPhase (shadowPhase unaryShadow_add_one)
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped ComplexConjugate

noncomputable section

theorem unconjugated_eq_neg_conjugate (k : ℝ) (F : Field) (x y : ℝ) :
    unconjugatedXi k F x y = -conj (conjugatedXi k F x y) := by
  rw [unconjugatedXi_eq_literal, conjugatedXi_eq_literal]
  simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem shadowPhase_im_pos : 0 < shadowPhase.im := by
  have h : periodCoefficient / 24 = ((Real.pi / 12 : ℝ) : ℂ) * Complex.I := by
    rw [periodCoefficient, Complex.ofReal_div]
    norm_num <;> ring
  rw [shadowPhase, h, Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

theorem conjugate_shadowPhase_ne : conj shadowPhase ≠ shadowPhase := by
  intro h
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  linarith [shadowPhase_im_pos]

theorem conjugate_unary_shadow_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    conj (unaryShadow (τ + 1)) = conj shadowPhase * conj (unaryShadow τ) := by
  rw [unaryShadow_add_one hτ, map_mul]

theorem conjugate_shadow_cannot_be_rescaled (c d : ℂ) (hd : d ≠ 0) :
    ¬ (∀ τ : ℂ, 0 < τ.im → c * conj (unaryShadow τ) = d * unaryShadow τ) := by
  intro h
  obtain ⟨τ, hτ, hNonzero⟩ := Paper8KroneckerShadowNonzero.unaryShadow_nonzero_on_upper_half_plane
  have hs : 0 < (τ + 1).im := by simpa using hτ
  have hBase := h τ hτ
  have hShift := h (τ + 1) hs
  rw [conjugate_unary_shadow_add_one hτ, unaryShadow_add_one hτ] at hShift
  have hZero : (conj shadowPhase - shadowPhase) * (d * unaryShadow τ) = 0 := by
    linear_combination hShift - conj shadowPhase * hBase
  exact (mul_ne_zero (sub_ne_zero.mpr conjugate_shadowPhase_ne) (mul_ne_zero hd hNonzero)) hZero

theorem unconjugated_shadow_value {F : Field} {x y : ℝ} {κ : ℂ}
    (h : conjugatedXi (1 / 2) F x y = κ * unaryShadow (complexPoint x y)) :
    unconjugatedXi (1 / 2) F x y = -conj κ * conj (unaryShadow (complexPoint x y)) := by
  rw [unconjugated_eq_neg_conjugate, h, map_mul, neg_mul]

theorem printed_conventions_incompatible_on_p338_shadow
    (F : Field) (κ κ' : ℂ) (hκ' : κ' ≠ 0)
    (h : ∀ x y : ℝ, 0 < y →
      conjugatedXi (1 / 2) F x y = κ * unaryShadow (complexPoint x y)) :
    ¬ (∀ x y : ℝ, 0 < y →
      unconjugatedXi (1 / 2) F x y = κ' * unaryShadow (complexPoint x y)) := by
  intro hUnbarred
  apply conjugate_shadow_cannot_be_rescaled (-conj κ) κ' hκ'
  intro τ hτ
  have hComplex : complexPoint τ.re τ.im = τ := Complex.re_add_im τ
  have hValue := hUnbarred τ.re τ.im hτ
  rw [unconjugated_shadow_value (h τ.re τ.im hτ), hComplex] at hValue
  exact hValue

end
end ManuscriptAudit.Paper8XiShadowConventions

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8XiShadowConventions.unconjugated_eq_neg_conjugate,
      ``ManuscriptAudit.Paper8XiShadowConventions.shadowPhase_im_pos,
      ``ManuscriptAudit.Paper8XiShadowConventions.conjugate_shadowPhase_ne,
      ``ManuscriptAudit.Paper8XiShadowConventions.conjugate_unary_shadow_add_one,
      ``ManuscriptAudit.Paper8XiShadowConventions.conjugate_shadow_cannot_be_rescaled,
      ``ManuscriptAudit.Paper8XiShadowConventions.unconjugated_shadow_value,
      ``ManuscriptAudit.Paper8XiShadowConventions.printed_conventions_incompatible_on_p338_shadow] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
