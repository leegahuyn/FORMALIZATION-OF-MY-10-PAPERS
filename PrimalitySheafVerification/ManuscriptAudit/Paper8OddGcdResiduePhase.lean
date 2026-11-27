import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Parity
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourResidueWeights

/-!
# Odd-gcd rescaling of the reciprocal residue phase

In a class d=g·u, 2k=g·(2ℓ) with odd g and reduced u, the
prefactor and the printed -d(1+(-1)^k)/8 phase differ from the
reduced row at ℓ by the sign (-1)^((g-1)/2) and the factor 1/g.
This finite identity supplies the odd-gcd part of the all-residue
arithmetic reduction.
-/

namespace ManuscriptAudit.Paper8OddGcdResiduePhase

open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8ContourResidueWeights (prefactor)

noncomputable section

def modulusSign (k : ℕ) : ℂ := (-1 : ℂ) ^ ((k + 1) / 2)

def oddFactorSign (g : ℕ) : ℂ := (-1 : ℂ) ^ ((g - 1) / 2)

def residuePhase (k d : ℕ) : ℂ :=
  Complex.exp (periodCoefficient * ((-(d : ℝ) / 8 * (1 + (-1 : ℝ) ^ k) : ℝ) : ℂ))

private theorem phase_odd {k : ℕ} (hk : Odd k) (d : ℕ) : residuePhase k d = 1 := by
  simp [residuePhase, hk.neg_one_pow]

private theorem phase_even {k : ℕ} (hk : Even k) (d : ℕ) :
    residuePhase k d = Complex.exp (periodCoefficient * ((-(d : ℝ) / 4 : ℝ) : ℂ)) := by
  have h : -(d : ℝ) / 8 * (1 + 1 : ℝ) = -(d : ℝ) / 4 := by ring
  rw [residuePhase, hk.neg_one_pow, h]

theorem exp_negative_half_period (m : ℕ) :
    Complex.exp (periodCoefficient * ((-(m : ℝ) / 2 : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  have h : periodCoefficient * ((-(m : ℝ) / 2 : ℝ) : ℂ) =
      (m : ℂ) * (-((Real.pi : ℂ) * Complex.I)) := by
    unfold periodCoefficient
    push_cast
    ring
  simp only [h, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

private theorem sign_odd_mul {g ℓ : ℕ} (hg : Odd g) (hℓ : Odd ℓ) :
    modulusSign (g * ℓ) = oddFactorSign g * modulusSign ℓ := by
  obtain ⟨r, hr⟩ := hg
  obtain ⟨s, hs⟩ := hℓ
  have hG : (g - 1) / 2 = r := by omega
  have hL : (ℓ + 1) / 2 = s + 1 := by omega
  have hM : g * ℓ + 1 = 2 * (r + (s + 1) + 2 * r * s) := by rw [hr, hs]; ring
  have hML : (g * ℓ + 1) / 2 = r + (s + 1) + 2 * r * s := by omega
  have hEven : Even (2 * r * s) := ⟨r * s, by ring⟩
  rw [modulusSign, oddFactorSign, modulusSign, hML, hG, hL, pow_add, hEven.neg_one_pow,
    mul_one, pow_add]

private theorem sign_even_mul {g ℓ : ℕ} (hg : Odd g) (hℓ : Even ℓ) :
    modulusSign (g * ℓ) = modulusSign ℓ := by
  obtain ⟨r, hr⟩ := hg
  obtain ⟨s, hs⟩ := hℓ
  have hL : (ℓ + 1) / 2 = s := by omega
  have hM : g * ℓ + 1 = 2 * (2 * r * s + s) + 1 := by rw [hr, hs]; ring
  have hML : (g * ℓ + 1) / 2 = 2 * r * s + s := by omega
  have hEven : Even (2 * r * s) := ⟨r * s, by ring⟩
  rw [modulusSign, modulusSign, hML, hL, pow_add, hEven.neg_one_pow, one_mul]

private theorem phase_even_odd_rescaling {g ℓ u : ℕ} (hg : Odd g) (hℓ : Even ℓ)
    (hu : Odd u) :
    residuePhase (g * ℓ) (g * u) = oddFactorSign g * residuePhase ℓ u := by
  have hGL : Even (g * ℓ) := by
    obtain ⟨s, hs⟩ := hℓ
    refine ⟨g * s, ?_⟩
    rw [hs]
    ring
  obtain ⟨r, hr⟩ := hg
  have hG : (g - 1) / 2 = r := by omega
  have hArg : -((g * u : ℕ) : ℝ) / 4 =
      -((r * u : ℕ) : ℝ) / 2 + -(u : ℝ) / 4 := by
    rw [hr]
    push_cast
    ring
  rw [phase_even hGL, phase_even hℓ, hArg, Complex.ofReal_add, mul_add, Complex.exp_add,
    exp_negative_half_period, oddFactorSign, hG, Nat.mul_comm r u, pow_mul, hu.neg_one_pow]

theorem odd_gcd_sign_mul_phase {g ℓ u : ℕ} (hg : Odd g) (hu : Odd u) :
    modulusSign (g * ℓ) * residuePhase (g * ℓ) (g * u) =
      oddFactorSign g * (modulusSign ℓ * residuePhase ℓ u) := by
  rcases Nat.even_or_odd ℓ with hℓ | hℓ
  · rw [sign_even_mul hg hℓ, phase_even_odd_rescaling hg hℓ hu]
    ring
  · rw [sign_odd_mul hg hℓ, phase_odd (hg.mul hℓ), phase_odd hℓ, mul_one, mul_one]

theorem odd_gcd_prefactor_mul_phase {g ℓ u : ℕ} (hg : Odd g) (hℓ : 0 < ℓ) (hu : Odd u) :
    prefactor (g * ℓ) * residuePhase (g * ℓ) (g * u) =
      (oddFactorSign g / (g : ℂ)) * (prefactor ℓ * residuePhase ℓ u) := by
  have hgn : g ≠ 0 := by
    obtain ⟨r, hr⟩ := hg
    omega
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hgn
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  change (modulusSign (g * ℓ) / ((g * ℓ : ℕ) : ℂ)) * residuePhase (g * ℓ) (g * u) =
    (oddFactorSign g / (g : ℂ)) * ((modulusSign ℓ / (ℓ : ℂ)) * residuePhase ℓ u)
  rw [Nat.cast_mul]
  calc
    _ = (modulusSign (g * ℓ) * residuePhase (g * ℓ) (g * u)) / ((g : ℂ) * (ℓ : ℂ)) := by ring
    _ = _ := by
      rw [odd_gcd_sign_mul_phase hg hu]
      field_simp [hgC, hℓC] <;> ring

end
end ManuscriptAudit.Paper8OddGcdResiduePhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddGcdResiduePhase.odd_gcd_sign_mul_phase,
      ``ManuscriptAudit.Paper8OddGcdResiduePhase.odd_gcd_prefactor_mul_phase] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
