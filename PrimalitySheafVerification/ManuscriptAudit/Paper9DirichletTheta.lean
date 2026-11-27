import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrincipalThetaPhase

/-! Every actual level-four Dirichlet-character theta is principal or identically zero. -/

namespace ManuscriptAudit.Paper9DirichletTheta

open Complex Paper9PrincipalThetaPhase Paper9PrincipalThetaStrip

noncomputable section

local instance : Fact (1 < 4) := ⟨by decide⟩

def series (ψ : DirichletCharacter ℂ 4) (τ : ℂ) : ℂ :=
  thetaWith (fun n => ψ (n : ZMod 4)) τ

theorem character_minus_one (ψ : DirichletCharacter ℂ 4) :
    ψ (-1 : ZMod 4) = 1 ∨ ψ (-1 : ZMod 4) = -1 := by
  have hs : ψ (-1 : ZMod 4) ^ 2 = 1 := by
    rw [← map_pow]
    norm_num
  have hp : (ψ (-1 : ZMod 4) - 1) * (ψ (-1 : ZMod 4) + 1) = 0 := by
    calc
      _ = ψ (-1 : ZMod 4) ^ 2 - 1 := by ring
      _ = _ := by rw [hs, sub_self]
  exact (mul_eq_zero.mp hp).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left

private theorem cast_eq_remainder (n : ℤ) :
    (n : ZMod 4) = ((n % 4 : ℤ) : ZMod 4) :=
  (ZMod.intCast_mod n 4).symm

private theorem odd_residue (n : ℤ) (hn : n % 2 = 1) :
    (n : ZMod 4) = 1 ∨ (n : ZMod 4) = -1 := by
  have he : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rw [cast_eq_remainder n]
  rcases he with he | he
  · exact Or.inl (by rw [he]; norm_num)
  · exact Or.inr (by rw [he]; decide)

private theorem even_residue_not_unit (n : ℤ) (hn : n % 2 ≠ 1) :
    ¬ IsUnit (n : ZMod 4) := by
  have he : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rw [cast_eq_remainder n]
  rcases he with he | he
  · simpa [he] using (not_isUnit_zero : ¬ IsUnit (0 : ZMod 4))
  · rw [he]
    intro h
    have hs := h.pow 2
    rw [show (((2 : ℤ) : ZMod 4) ^ 2) = 0 by decide] at hs
    exact not_isUnit_zero hs

theorem series_eq_principal (ψ : DirichletCharacter ℂ 4) (hψ : ψ (-1 : ZMod 4) = 1) :
    series ψ = principalTheta := by
  funext τ
  unfold series thetaWith principalTheta
  apply tsum_congr
  intro n
  have hCoefficient : ψ (n : ZMod 4) = principalChar n := by
    by_cases ho : n % 2 = 1
    · rcases odd_residue n ho with hn | hn
      · simp [hn, principalChar, ho]
      · simp [hn, hψ, principalChar, ho]
    · simp only [principalChar, if_neg ho]
      exact MulChar.map_nonunit ψ (even_residue_not_unit n ho)
  exact congrArg (fun u : ℂ => u * jacobiTheta₂_term n 0 τ) hCoefficient

theorem series_eq_zero (ψ : DirichletCharacter ℂ 4) (hψ : ψ (-1 : ZMod 4) = -1) :
    series ψ = 0 := by
  funext τ
  let a (n : ℤ) := ψ (n : ZMod 4) * jacobiTheta₂_term n 0 τ
  have ha (n : ℤ) : a (-n) = -a n := by
    have hc : ψ ((-n : ℤ) : ZMod 4) = -ψ (n : ZMod 4) := by
      rw [Int.cast_neg, ← neg_one_mul (n : ZMod 4), map_mul, hψ, neg_one_mul]
    have hTerm : jacobiTheta₂_term (-n) 0 τ = jacobiTheta₂_term n 0 τ := by
      simp only [jacobiTheta₂_term, mul_zero, zero_add, Int.cast_neg, neg_sq]
    change ψ ((-n : ℤ) : ZMod 4) * jacobiTheta₂_term (-n) 0 τ =
      -(ψ (n : ZMod 4) * jacobiTheta₂_term n 0 τ)
    rw [hc, hTerm, neg_mul]
  have he : (∑' n, a n) = -(∑' n, a n) := by
    calc
      _ = ∑' n : ℤ, a (-n) := ((Equiv.neg ℤ).tsum_eq a).symm
      _ = ∑' n : ℤ, -a n := tsum_congr ha
      _ = _ := tsum_neg
  change (∑' n, a n) = 0
  apply Complex.ext
  · have h := congrArg Complex.re he
    simp only [Complex.neg_re] at h
    simp only [Complex.zero_re]
    linarith
  · have h := congrArg Complex.im he
    simp only [Complex.neg_im] at h
    simp only [Complex.zero_im]
    linarith

theorem series_eq_principal_or_zero (ψ : DirichletCharacter ℂ 4) :
    series ψ = principalTheta ∨ series ψ = 0 :=
  (character_minus_one ψ).imp (series_eq_principal ψ) (series_eq_zero ψ)

end
end ManuscriptAudit.Paper9DirichletTheta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9DirichletTheta.character_minus_one,
      ``ManuscriptAudit.Paper9DirichletTheta.series_eq_principal,
      ``ManuscriptAudit.Paper9DirichletTheta.series_eq_zero,
      ``ManuscriptAudit.Paper9DirichletTheta.series_eq_principal_or_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
