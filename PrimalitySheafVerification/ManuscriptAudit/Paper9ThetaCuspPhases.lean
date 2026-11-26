import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8XiShadow
import PrimalitySheafVerification.ManuscriptAudit.ThreeCuspNeighborhoods

/-!
# Width-two cusp phases for the standard Jacobi theta multiplier

Paper 9, physical page 406, Q2.D. In the three actual level-two
cusp charts (infinity, zero, one), the standard positive Jacobi theta
profile has width-two translation phases (1, 1, i). We compute the
actual profiles using the native one- and two-variable Jacobi theta
functions. Thus exactly two normalized profiles are periodic. This
is a calculation of parabolic phases for this multiplier.
-/

namespace ManuscriptAudit.Paper9ThetaCuspPhases

open ModularGroup (S T)
open scoped UpperHalfPlane

noncomputable section

/-- The weight factor for the zero and one cusp charts. -/
def thetaWeightFactor (z : ℍ) : ℂ :=
  (-Complex.I * (z : ℂ)) ^ (1 / 2 : ℂ)

private theorem coe_ne_zero (z : ℍ) : (z : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  exact z.im_pos.ne' (by simpa using hi)

private theorem thetaWeightFactor_ne_zero (z : ℍ) : thetaWeightFactor z ≠ 0 := by
  exact Complex.cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (coe_ne_zero z)))

/-- The native half-shifted Jacobi theta profile. -/
def thetaHalfShift (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ

theorem thetaHalfShift_add_two (τ : ℂ) :
    thetaHalfShift (τ + 2) = Complex.I * thetaHalfShift τ := by
  unfold thetaHalfShift
  rw [show (τ + 2) / 2 = τ / 2 + 1 by ring,
    jacobiTheta₂_add_right, jacobiTheta₂_add_left,
    show (Real.pi : ℂ) * Complex.I * (τ + 2) / 4 =
      (Real.pi : ℂ) * Complex.I * τ / 4 + (Real.pi : ℂ) / 2 * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  ring

theorem int_square_eq_add_twice (n : ℤ) : ∃ k : ℤ, n ^ 2 = n + 2 * k := by
  let m := n / 2
  have h : n = 2 * m ∨ n = 2 * m + 1 := by
    dsimp [m]
    omega
  rcases h with h | h
  · refine ⟨2 * m ^ 2 - m, ?_⟩
    rw [h]
    ring
  · refine ⟨2 * m ^ 2 + m, ?_⟩
    rw [h]
    ring

theorem jacobiTheta_add_one_profile (τ : ℂ) :
    jacobiTheta (τ + 1) = jacobiTheta₂ (1 / 2) τ := by
  unfold jacobiTheta jacobiTheta₂ jacobiTheta₂_term
  apply tsum_congr
  intro n
  obtain ⟨k, hk⟩ := int_square_eq_add_twice n
  have hkC : (n : ℂ) ^ 2 = (n : ℂ) + 2 * (k : ℂ) := by exact_mod_cast hk
  calc
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2) +
        (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ +
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      congr 1
      linear_combination ((Real.pi : ℂ) * Complex.I) * hkC
    _ = _ := by rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The S transformation of the shifted profile, with its actual
weight factor and the complex power used by Mathlib. -/
theorem thetaHalfShift_inversion (z : ℍ) :
    jacobiTheta₂ (1 / 2) (-1 / (z : ℂ)) =
      thetaWeightFactor z * thetaHalfShift (z : ℂ) := by
  let t : ℂ := z
  let a : ℂ := (Real.pi : ℂ) * Complex.I * t / 4
  let w : ℂ := thetaWeightFactor z
  have ht : t ≠ 0 := coe_ne_zero z
  have hw : w ≠ 0 := thetaWeightFactor_ne_zero z
  have hf := jacobiTheta₂_functional_equation (t / 2) t
  change jacobiTheta₂ (t / 2) t = 1 / w *
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (t / 2) ^ 2 / t) *
      jacobiTheta₂ (t / 2 / t) (-1 / t) at hf
  have hArg : t / 2 / t = (1 / 2 : ℂ) := by field_simp [ht]
  have hExp : -(Real.pi : ℂ) * Complex.I * (t / 2) ^ 2 / t = -a := by
    dsimp [a]
    field_simp [ht] <;> ring
  rw [hArg, hExp] at hf
  change jacobiTheta₂ (1 / 2) (-1 / t) = w * (Complex.exp a * jacobiTheta₂ (t / 2) t)
  rw [hf]
  symm
  calc
    _ = (w * (1 / w)) * (Complex.exp a * Complex.exp (-a)) *
        jacobiTheta₂ (1 / 2) (-1 / t) := by ring
    _ = _ := by
      simp only [one_div, mul_inv_cancel₀ hw, ← Complex.exp_add, add_neg_cancel,
        Complex.exp_zero, one_mul]

private theorem coe_TS_smul (z : ℍ) :
    (((T * S) • z : ℍ) : ℂ) = -1 / (z : ℂ) + 1 := by
  rw [mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd,
    UpperHalfPlane.modular_S_smul]
  simp [neg_div, one_div, add_comm]

theorem theta_TS_pullback (z : ℍ) :
    jacobiTheta (((T * S) • z : ℍ) : ℂ) =
      thetaWeightFactor z * thetaHalfShift (z : ℂ) := by
  rw [coe_TS_smul, jacobiTheta_add_one_profile, thetaHalfShift_inversion]

theorem thetaHalfShift_I_ne_zero : thetaHalfShift Complex.I ≠ 0 := by
  intro h
  let z : ℍ := ⟨Complex.I, by simp⟩
  have he := thetaHalfShift_inversion z
  change jacobiTheta₂ (1 / 2) (-1 / Complex.I) =
    thetaWeightFactor z * thetaHalfShift Complex.I at he
  have hI : (-1 : ℂ) / Complex.I = Complex.I :=
    (div_eq_iff Complex.I_ne_zero).2 Complex.I_mul_I.symm
  rw [h, mul_zero, hI] at he
  apply Paper8XiShadow.printedTheta_at_I_ne_zero
  change jacobiTheta₂ ((-1 : ℂ) / 2) Complex.I = 0
  rw [neg_div, jacobiTheta₂_neg_left]
  exact he

/-- Jacobi theta in each of the three verified charts, after removing
the weight factor. The chart order is infinity, zero, one. -/
def normalizedProfile (i : Fin 3) (z : ℍ) : ℂ :=
  jacobiTheta ((ThreeCuspNeighborhoods.chart i • z : ℍ) : ℂ) /
    (if i = 0 then 1 else thetaWeightFactor z)

theorem normalizedProfile_zero (z : ℍ) :
    normalizedProfile 0 z = jacobiTheta (z : ℂ) := by
  simp [normalizedProfile, ThreeCuspNeighborhoods.chart]

theorem normalizedProfile_one (z : ℍ) :
    normalizedProfile 1 z = jacobiTheta (z : ℂ) := by
  change jacobiTheta ((S • z : ℍ) : ℂ) / thetaWeightFactor z = _
  apply (div_eq_iff (thetaWeightFactor_ne_zero z)).2
  rw [jacobiTheta_S_smul]
  exact mul_comm _ _

theorem normalizedProfile_two (z : ℍ) :
    normalizedProfile 2 z = thetaHalfShift (z : ℂ) := by
  change jacobiTheta (((T * S) • z : ℍ) : ℂ) / thetaWeightFactor z = _
  apply (div_eq_iff (thetaWeightFactor_ne_zero z)).2
  rw [theta_TS_pullback]
  exact mul_comm _ _

def parabolicPhase : Fin 3 → ℂ := ![(1 : ℂ), 1, Complex.I]

private theorem coe_T_sq_smul (z : ℍ) : ((T ^ (2 : ℕ) • z : ℍ) : ℂ) = (z : ℂ) + 2 := by
  have h : T ^ (2 : ℕ) = T ^ (2 : ℤ) := rfl
  simp_rw [h, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_num [add_comm]

/-- Width-two parabolic translation of the actual normalized cusp profiles. -/
theorem normalizedProfile_width_two (i : Fin 3) (z : ℍ) :
    normalizedProfile i (T ^ (2 : ℕ) • z) = parabolicPhase i * normalizedProfile i z := by
  fin_cases i
  · simpa [parabolicPhase, normalizedProfile_zero] using jacobiTheta_T_sq_smul z
  · simpa [parabolicPhase, normalizedProfile_one] using jacobiTheta_T_sq_smul z
  · change normalizedProfile 2 (T ^ (2 : ℕ) • z) = Complex.I * normalizedProfile 2 z
    calc
      _ = thetaHalfShift ((T ^ (2 : ℕ) • z : ℍ) : ℂ) := normalizedProfile_two _
      _ = thetaHalfShift ((z : ℂ) + 2) := congrArg thetaHalfShift (coe_T_sq_smul z)
      _ = Complex.I * thetaHalfShift (z : ℂ) := thetaHalfShift_add_two _
      _ = _ := congrArg (fun c => Complex.I * c) (normalizedProfile_two z).symm

def PeriodicCusp (i : Fin 3) : Prop :=
  ∀ z : ℍ, normalizedProfile i (T ^ (2 : ℕ) • z) = normalizedProfile i z

theorem periodicCusp_iff (i : Fin 3) : PeriodicCusp i ↔ i ≠ 2 := by
  fin_cases i
  · have h : PeriodicCusp 0 := fun z => by
      simpa [parabolicPhase] using normalizedProfile_width_two 0 z
    simp [h]
  · have h : PeriodicCusp 1 := fun z => by
      simpa [parabolicPhase] using normalizedProfile_width_two 1 z
    simp [h]
  · have hn : ¬ PeriodicCusp 2 := by
      intro h
      let z : ℍ := ⟨Complex.I, by simp⟩
      have hz : normalizedProfile 2 z ≠ 0 := by
        rw [normalizedProfile_two]
        exact thetaHalfShift_I_ne_zero
      have he := h z
      rw [normalizedProfile_width_two] at he
      have hm : Complex.I * normalizedProfile 2 z = 1 * normalizedProfile 2 z := by
        simpa [parabolicPhase] using he
      have hOne := mul_right_cancel₀ hz hm
      have hRe := congrArg Complex.re hOne
      norm_num at hRe
    simp [hn]

def periodicCusps : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter PeriodicCusp

theorem periodicCusps_eq : periodicCusps = ({0, 1} : Finset (Fin 3)) := by
  classical
  ext i
  simp only [periodicCusps, Finset.mem_filter, Finset.mem_univ, true_and, periodicCusp_iff]
  fin_cases i <;> decide

theorem periodicCusps_card : periodicCusps.card = 2 := by
  rw [periodicCusps_eq] <;> decide

end

end ManuscriptAudit.Paper9ThetaCuspPhases

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9ThetaCuspPhases.thetaHalfShift_add_two,
      ``ManuscriptAudit.Paper9ThetaCuspPhases.jacobiTheta_add_one_profile,
      ``ManuscriptAudit.Paper9ThetaCuspPhases.thetaHalfShift_inversion,
      ``ManuscriptAudit.Paper9ThetaCuspPhases.theta_TS_pullback,
      ``ManuscriptAudit.Paper9ThetaCuspPhases.thetaHalfShift_I_ne_zero,
      ``ManuscriptAudit.Paper9ThetaCuspPhases.normalizedProfile_width_two,
      ``ManuscriptAudit.Paper9ThetaCuspPhases.periodicCusp_iff,
      ``ManuscriptAudit.Paper9ThetaCuspPhases.periodicCusps_card] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
