import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrincipalThetaStrip

/-! The nonzero principal modulo-four theta has the exact parabolic phase -1. -/

namespace ManuscriptAudit.Paper9PrincipalThetaPhase

open Complex Paper9PrincipalThetaStrip

noncomputable section

def thetaWith (a : ℤ → ℂ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, a n * jacobiTheta₂_term n 0 τ

theorem thetaWith_add_one_of_odd_support (a : ℤ → ℂ)
    (ha : ∀ n, n % 2 ≠ 1 → a n = 0) (τ : ℂ) :
    thetaWith a (τ + 1) = -thetaWith a τ := by
  unfold thetaWith
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  by_cases hn : n % 2 = 1
  · simp only [principalChar, if_pos hn, one_mul, jacobiTheta₂_term, mul_zero, zero_add]
    have ho : Odd (n ^ (2 : ℕ)) := (Int.odd_iff.mpr hn).pow
    have hp : (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ + 1) =
        (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ +
          ((n ^ (2 : ℕ) : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hp, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I, ho.neg_one_zpow]
    ring
  · simp only [ha n hn, zero_mul, neg_zero]

theorem principalTheta_add_one (τ : ℂ) : principalTheta (τ + 1) = -principalTheta τ :=
  thetaWith_add_one_of_odd_support principalChar (fun n h => by simp [principalChar, h]) τ

private theorem even_cast_mod_four_not_unit (n : ℤ) (hn : n % 2 ≠ 1) :
    ¬ IsUnit (n : ZMod 4) := by
  intro h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, n = m + m := ⟨n / 2, by omega⟩
  have hzero : (n : ZMod 4) ^ 2 = 0 := by
    rw [hm]; push_cast
    calc
      _ = (4 : ZMod 4) * (m : ZMod 4) ^ 2 := by ring
      _ = _ := by norm_num
  have hp := h.pow 2
  rw [hzero] at hp
  exact not_isUnit_zero hp

theorem dirichletTheta_add_one (ψ : DirichletCharacter ℂ 4) (τ : ℂ) :
    thetaWith (fun n => ψ (n : ZMod 4)) (τ + 1) =
      -thetaWith (fun n => ψ (n : ZMod 4)) τ :=
  thetaWith_add_one_of_odd_support _
    (fun n hn => MulChar.map_nonunit ψ (even_cast_mod_four_not_unit n hn)) τ

theorem principalTheta_re_I_pos : 0 < (principalTheta Complex.I).re := by
  have h := principalTheta_re_axis_lower 1 zero_lt_one
  simp only [Complex.ofReal_one, one_mul, mul_one] at h
  exact (Real.exp_pos _).trans_le h

theorem principalTheta_not_phase_one :
    principalTheta (Complex.I + 1) ≠ principalTheta Complex.I := by
  rw [principalTheta_add_one]
  intro h
  have e := congrArg Complex.re h
  simp only [Complex.neg_re] at e
  linarith [principalTheta_re_I_pos]

theorem principalTheta_phase_unique (χ : ℂ)
    (h : ∀ τ : ℂ, 0 < τ.im → principalTheta (τ + 1) = χ * principalTheta τ) :
    χ = -1 := by
  have hne : principalTheta Complex.I ≠ 0 := by
    intro hz
    have hpos := principalTheta_re_I_pos
    rw [hz, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  have h' := h Complex.I (by simp)
  rw [principalTheta_add_one, ← neg_one_mul] at h'
  exact (mul_right_cancel₀ hne h').symm

end
end ManuscriptAudit.Paper9PrincipalThetaPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9PrincipalThetaPhase.thetaWith_add_one_of_odd_support,
      ``ManuscriptAudit.Paper9PrincipalThetaPhase.dirichletTheta_add_one,
      ``ManuscriptAudit.Paper9PrincipalThetaPhase.principalTheta_add_one,
      ``ManuscriptAudit.Paper9PrincipalThetaPhase.principalTheta_re_I_pos,
      ``ManuscriptAudit.Paper9PrincipalThetaPhase.principalTheta_not_phase_one,
      ``ManuscriptAudit.Paper9PrincipalThetaPhase.principalTheta_phase_unique] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
