import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindReferenceFrequency
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspRows
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelZeroMode

/-!
# The same-cusp character twist at even reduced Fourier rows

For D divisible by four, the frequency shift -D/4 gives i times the
Dirichlet-weighted unshifted reference sum. The character is the
actual lower-right character of the level-four subgroup.
-/

namespace ManuscriptAudit.Paper8EvenReducedCharacterPhase

open Paper8OddCrossCuspRows (chiFour)
open Paper8EtaLevelZeroMode (referenceEntry)
open Paper8ContourResidueWeights (dedekindSum)
open Paper8DedekindReferenceFrequency (referenceSum)

noncomputable section

def twistedReferenceZero (D : ℕ) : ℂ :=
  ∑ d ∈ (Finset.univ.filter (fun d : Fin D => Nat.Coprime d.val D)),
    (chiFour (d.val : ZMod 4) : ℂ) * referenceEntry D (d.val : ℤ)

private theorem i_pow_odd_character (n : ℕ) (hOdd : Odd n) :
    Complex.I ^ n = Complex.I * (chiFour (n : ZMod 4) : ℂ) := by
  have hMod : n % 4 = 1 ∨ n % 4 = 3 := by
    obtain ⟨j, hj⟩ := hOdd
    omega
  rw [Complex.I_pow_eq_pow_mod]
  obtain h | h := hMod
  · have hCast : (n : ZMod 4) = (1 : ℕ) := (ZMod.natCast_eq_natCast_iff' n 1 4).2 (by simpa using h)
    simp [h, hCast, chiFour]
  · have hCast : (n : ZMod 4) = (3 : ℕ) := (ZMod.natCast_eq_natCast_iff' n 3 4).2 (by simpa using h)
    rw [h, hCast, Complex.I_pow_three]
    have hChi : chiFour ((3 : ℕ) : ZMod 4) = -1 := by decide
    rw [hChi]
    simp

theorem referenceSum_quarter_shift_eq {D : ℕ} (hD : 0 < D) (hFour : 4 ∣ D) :
    referenceSum D (-(D : ℝ) / 4) = Complex.I * twistedReferenceZero D := by
  have hDReal : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hTwo : 2 ∣ D := (by decide : 2 ∣ 4).trans hFour
  unfold referenceSum twistedReferenceZero
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hCoprime : Nat.Coprime d.val D := (Finset.mem_filter.mp hd).2
  have hOdd : Odd d.val := (hCoprime.of_dvd_right hTwo).odd_of_right
  have hArg : (dedekindSum (d.val : ℤ) D : ℝ) -
      2 * (-(D : ℝ) / 4) * (d.val : ℝ) / (D : ℝ) =
      (dedekindSum (d.val : ℤ) D : ℝ) + (d.val : ℝ) / 2 := by
    field_simp [hDReal] <;> ring
  rw [hArg, Complex.ofReal_add, mul_add, Complex.exp_add]
  have hExp : Complex.exp ((Real.pi : ℂ) * Complex.I * (((d.val : ℝ) / 2 : ℝ) : ℂ)) =
      Complex.I ^ d.val := by
    rw [show (Real.pi : ℂ) * Complex.I * (((d.val : ℝ) / 2 : ℝ) : ℂ) =
      (d.val : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) by push_cast; ring,
      Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  rw [hExp, i_pow_odd_character d.val hOdd, referenceEntry]
  ring

end
end ManuscriptAudit.Paper8EvenReducedCharacterPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8EvenReducedCharacterPhase.referenceSum_quarter_shift_eq
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
