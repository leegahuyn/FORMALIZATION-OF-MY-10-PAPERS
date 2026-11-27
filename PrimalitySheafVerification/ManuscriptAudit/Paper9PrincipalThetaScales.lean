import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrincipalThetaStrip

/-! The actual principal level-four theta is a difference of thetas at two scales. -/

namespace ManuscriptAudit.Paper9PrincipalThetaScales

open Complex Set Paper9PrincipalThetaStrip

noncomputable section

private def evenTerm (τ : ℂ) (n : ℤ) : ℂ :=
  if n % 2 = 0 then jacobiTheta₂_term n 0 τ else 0

private theorem evenTerm_two_mul (τ : ℂ) (n : ℤ) :
    evenTerm τ (2 * n) = jacobiTheta₂_term n 0 (4 * τ) := by
  have h : (2 * n) % 2 = 0 := by omega
  simp only [evenTerm, if_pos h, jacobiTheta₂_term, mul_zero, zero_add, Int.cast_mul,
    Int.cast_ofNat]
  congr 1
  ring

private theorem evenTerm_tsum (τ : ℂ) :
    (∑' n : ℤ, evenTerm τ n) = jacobiTheta (4 * τ) := by
  let f (n : ℤ) := 2 * n
  have hf : Function.Injective f := by
    intro m n he
    change 2 * m = 2 * n at he
    omega
  have hs : Function.support (evenTerm τ) ⊆ range f := by
    intro n hn
    have h : n % 2 = 0 := by
      by_contra h
      exact hn (by simp [evenTerm, h])
    exact ⟨n / 2, by dsimp [f]; omega⟩
  have he := hf.tsum_eq hs
  calc
    _ = ∑' n : ℤ, evenTerm τ (2 * n) := he.symm
    _ = ∑' n : ℤ, jacobiTheta₂_term n 0 (4 * τ) := tsum_congr (evenTerm_two_mul τ)
    _ = _ := by rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂]

theorem principalTheta_eq_difference (τ : ℂ) (hτ : 0 < τ.im) :
    principalTheta τ = jacobiTheta τ - jacobiTheta (4 * τ) := by
  let a (n : ℤ) := principalChar n * jacobiTheta₂_term n 0 τ
  have hnorm : Summable (fun n : ℤ => ‖jacobiTheta₂_term n 0 τ‖) :=
    (summable_norm_iff (E := ℂ)).2 ((summable_jacobiTheta₂_term_iff 0 τ).2 hτ)
  have ha : Summable a := hnorm.of_norm_bounded fun n => by
    by_cases h : n % 2 = 1 <;> simp [a, principalChar, h]
  have hb : Summable (evenTerm τ) := hnorm.of_norm_bounded fun n => by
    by_cases h : n % 2 = 0 <;> simp [evenTerm, h]
  have hc (n : ℤ) : a n + evenTerm τ n = jacobiTheta₂_term n 0 τ := by
    by_cases h : n % 2 = 0
    · have h' : n % 2 ≠ 1 := by omega
      simp [a, evenTerm, principalChar, h, h']
    · have h' : n % 2 = 1 := by omega
      simp [a, evenTerm, principalChar, h, h']
  apply eq_sub_of_add_eq
  calc
    _ = (∑' n : ℤ, a n) + ∑' n : ℤ, evenTerm τ n := by
      rw [evenTerm_tsum]
      rfl
    _ = ∑' n : ℤ, (a n + evenTerm τ n) := (ha.tsum_add hb).symm
    _ = ∑' n : ℤ, jacobiTheta₂_term n 0 τ := tsum_congr hc
    _ = _ := by rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂]

end
end ManuscriptAudit.Paper9PrincipalThetaScales

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9PrincipalThetaScales.principalTheta_eq_difference
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
