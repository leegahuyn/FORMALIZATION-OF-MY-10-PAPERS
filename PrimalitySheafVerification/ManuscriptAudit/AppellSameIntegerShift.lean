import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Simultaneous Appell shifts for the stated Paper 8 blocks

The two blocks with indices (0,0) and (1,0) have identical functions.
The literal Appell numerator shifts by reindexing its bilateral series.
The genuine odd theta factor has the matching quasi-period, so the
two factors cancel in the quotient. The formula follows the Appell
function and odd theta of Zwegers, Mock Theta Functions, §§1.2–1.3.
-/

namespace ManuscriptAudit.AppellSameIntegerShift

noncomputable section

private abbrev phase (z : ℂ) := (Real.pi : ℂ) * Complex.I * z

private theorem expPhase_add (a b : ℂ) :
    Complex.exp (phase (a + b)) = Complex.exp (phase a) * Complex.exp (phase b) := by
  rw [mul_add, Complex.exp_add]

private theorem expPhase_sub_one (a : ℂ) :
    Complex.exp (phase (a - 1)) = -Complex.exp (phase a) := by
  rw [sub_eq_add_neg, expPhase_add]
  have h : phase (-1) = -((Real.pi : ℂ) * Complex.I) := by ring
  rw [h, Complex.exp_neg_pi_mul_I, mul_neg_one]

def numeratorTerm (u v τ : ℂ) (n : ℤ) : ℂ :=
  ((-1 : ℂ) ^ n * Complex.exp (phase
    (((n : ℂ) ^ 2 + n) * τ + 2 * (n : ℂ) * v))) /
    (1 - Complex.exp (phase (2 * (u + (n : ℂ) * τ))))

def numerator (u v τ : ℂ) : ℂ := ∑' n : ℤ, numeratorTerm u v τ n

theorem numeratorTerm_simultaneous_shift (u v τ : ℂ) (n : ℤ) :
    numeratorTerm (u + τ) (v + τ) τ n =
      Complex.exp (phase (-2 * (τ + v) - 1)) * numeratorTerm u v τ (n + 1) := by
  have hDen : u + τ + (n : ℂ) * τ = u + ((n + 1 : ℤ) : ℂ) * τ := by
    push_cast
    ring
  have hNum : ((n : ℂ) ^ 2 + n) * τ + 2 * (n : ℂ) * (v + τ) =
      -2 * (τ + v) + ((((n + 1 : ℤ) : ℂ) ^ 2 + ((n + 1 : ℤ) : ℂ)) * τ +
        2 * ((n + 1 : ℤ) : ℂ) * v) := by
    push_cast
    ring
  have hSign : (-1 : ℂ) ^ (n + 1) = -((-1 : ℂ) ^ n) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one, mul_neg_one]
  unfold numeratorTerm
  rw [hDen, hNum, expPhase_add, expPhase_sub_one, hSign]
  simp only [div_eq_mul_inv]
  ring

theorem numerator_simultaneous_shift (u v τ : ℂ) :
    numerator (u + τ) (v + τ) τ =
      Complex.exp (phase (-2 * (τ + v) - 1)) * numerator u v τ := by
  unfold numerator
  simp_rw [numeratorTerm_simultaneous_shift, tsum_mul_left]
  rw [(Equiv.addRight (1 : ℤ)).tsum_eq (numeratorTerm u v τ)]

/-- The genuine odd theta in the Appell denominator. -/
def oddTheta (v τ : ℂ) : ℂ :=
  Complex.exp (phase (τ / 4 + v + 1 / 2)) * jacobiTheta₂ (v + 1 / 2 + τ / 2) τ

theorem oddTheta_hasSum (v τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => Complex.exp (phase
      (((n : ℂ) + 1 / 2) ^ 2 * τ + 2 * ((n : ℂ) + 1 / 2) * (v + 1 / 2))))
      (oddTheta v τ) := by
  have h := (hasSum_jacobiTheta₂_term (v + 1 / 2 + τ / 2) hτ).mul_left
    (Complex.exp (phase (τ / 4 + v + 1 / 2)))
  have hTerm (n : ℤ) : Complex.exp (phase
      (((n : ℂ) + 1 / 2) ^ 2 * τ + 2 * ((n : ℂ) + 1 / 2) * (v + 1 / 2))) =
      Complex.exp (phase (τ / 4 + v + 1 / 2)) *
        jacobiTheta₂_term (v + 1 / 2 + τ / 2) τ n := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hTerm]
  exact h

theorem oddTheta_shift (v τ : ℂ) :
    oddTheta (v + τ) τ = Complex.exp (phase (-τ - 2 * v - 1)) * oddTheta v τ := by
  have hs : v + τ + 1 / 2 + τ / 2 = (v + 1 / 2 + τ / 2) + τ := by ring
  unfold oddTheta
  rw [hs, jacobiTheta₂_add_left']
  have hphase : phase (τ / 4 + (v + τ) + 1 / 2) +
      (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (v + 1 / 2 + τ / 2))) =
      phase (-τ - 2 * v - 1) + phase (τ / 4 + v + 1 / 2) := by ring
  calc
    _ = Complex.exp (phase (τ / 4 + (v + τ) + 1 / 2) +
        (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (v + 1 / 2 + τ / 2)))) *
        jacobiTheta₂ (v + 1 / 2 + τ / 2) τ := by rw [Complex.exp_add, mul_assoc]
    _ = _ := by rw [hphase, Complex.exp_add, mul_assoc]

/-- The Appell function specified by the bilateral numerator and odd theta. -/
def mu (u v τ : ℂ) : ℂ :=
  Complex.exp (phase u) * numerator u v τ / oddTheta v τ

theorem mu_simultaneous_shift (u v τ : ℂ) :
    mu (u + τ) (v + τ) τ = mu u v τ := by
  have h : Complex.exp (phase (u + τ)) * Complex.exp (phase (-2 * (τ + v) - 1)) =
      Complex.exp (phase (-τ - 2 * v - 1)) * Complex.exp (phase u) := by
    rw [← expPhase_add, ← expPhase_add]
    congr 1
    ring
  unfold mu
  rw [numerator_simultaneous_shift, oddTheta_shift, ← mul_assoc, h, mul_assoc]
  exact mul_div_mul_left _ _ (Complex.exp_ne_zero _)

/-- The two displayed manuscript blocks with r=0 coincide as functions. -/
theorem paper8_first_two_blocks_equal :
    (fun τ : ℂ => mu (τ / 2 + τ) (τ / 2 + 1 / 2 + τ) τ) =
      fun τ : ℂ => mu (τ / 2) (τ / 2 + 1 / 2) τ := by
  funext τ
  exact mu_simultaneous_shift (τ / 2) (τ / 2 + 1 / 2) τ

end

end ManuscriptAudit.AppellSameIntegerShift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.AppellSameIntegerShift.numeratorTerm_simultaneous_shift,
      ``ManuscriptAudit.AppellSameIntegerShift.numerator_simultaneous_shift,
      ``ManuscriptAudit.AppellSameIntegerShift.oddTheta_hasSum,
      ``ManuscriptAudit.AppellSameIntegerShift.oddTheta_shift,
      ``ManuscriptAudit.AppellSameIntegerShift.mu_simultaneous_shift,
      ``ManuscriptAudit.AppellSameIntegerShift.paper8_first_two_blocks_equal] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
