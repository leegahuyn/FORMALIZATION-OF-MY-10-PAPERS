import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossWindowIntegrability
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossHeightWindow

/-! A finite log-height pairing against the actual first cross Fourier coefficient is nonzero. -/

namespace ManuscriptAudit.Paper8OddCrossWindowPairing

open Filter MeasureTheory Set
open Paper8OddCrossWindowIntegrability Paper8OddCrossHeightWindow
open Paper8OddCrossLocalizedKernel Paper8OddCrossLocalizedRows Paper8OddCrossLocalizedFourier
open Paper8OddCrossCuspCutoff Paper8OddCrossFirstCoefficient Paper8OddCrossPoincareConvergence
open Paper8OddCrossPoincareUnfold
open scoped Topology

noncomputable section

def crossCutoffFourierAtLogHeight (q t : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..(1 : ℝ), ∑' i : CrossIndex,
    oddCrossHeightCutoffFourierTerm q (pointAtHeight x (Real.exp_pos t)) i

def crossHeightTestPairing (q T : ℝ) : ℂ :=
  ∫ t in Ioo (-T) T, (Real.exp (-t) : ℂ) * crossCutoffFourierAtLogHeight q t

private theorem cutoff_fourier_eq_first {q : ℝ} (hq : 0 < q) (t : ℝ)
    (hKill : ∀ (D : ℕ), 2 ≤ D → ∀ u : ℝ,
      crossHeightCutoffKernel q (Real.exp t) (2 * (D : ℝ)) u = 0) :
    crossCutoffFourierAtLogHeight q t = firstCrossCutoffCoefficient q t := by
  rw [crossCutoffFourierAtLogHeight, odd_cross_height_cutoff_fourier_expansion hq (Real.exp_pos t)]
  have hSupport (D : ℕ) (hD : D ∉ ({0} : Finset ℕ)) :
      crossSum (Nat.succ_pos D) *
        ∫ u : ℝ, crossHeightCutoffKernel q (Real.exp t) (2 * ((D + 1 : ℕ) : ℝ)) u = 0 := by
    have hD0 : D ≠ 0 := by simpa only [Finset.mem_singleton] using hD
    simp only [hKill (D + 1) (by omega), integral_zero, mul_zero]
  rw [tsum_eq_sum hSupport, Finset.sum_singleton]
  simp only [zero_add, Nat.cast_one, mul_one, crossSum_one, one_mul, firstCrossCutoffCoefficient]

theorem exists_nonzero_crossHeightTestPairing :
    ∃ q T : ℝ, 1 / 16 < q ∧ q < 1 / 4 ∧ 0 < T ∧ crossHeightTestPairing q T ≠ 0 := by
  obtain ⟨q, T, z, hqLo, hqHi, hT, hz, hW⟩ := exists_cross_cutoff_logHeight_window
  have hq : 0 < q := (by norm_num : (0 : ℝ) < 1 / 16).trans hqLo
  let W := Ioo (-T) T
  let G (t : ℝ) := (Real.exp (-t) : ℂ) * firstCrossCutoffCoefficient q t
  let R (t : ℝ) := (z * G t).re
  have hG : IntegrableOn G W := weighted_firstCrossCutoffCoefficient_integrableOn hq hT.le
  have hZI : IntegrableOn (fun t => z * G t) W := hG.const_mul z
  have hR : IntegrableOn R W := hZI.re
  have hPos (t : ℝ) (ht : t ∈ W) : 0 < R t := by
    have ht' : |t| < T := abs_lt.mpr ht
    have hFirst := (hW t ht').2
    change 0 < (z * ((Real.exp (-t) : ℂ) * firstCrossCutoffCoefficient q t)).re
    rw [mul_left_comm z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (Real.exp_pos _) hFirst
  have hR₊ : 0 ≤ᵐ[(volume : Measure ℝ).restrict W] R := by
    filter_upwards [ae_restrict_mem (show MeasurableSet W from measurableSet_Ioo)] with t ht
    exact (hPos t ht).le
  have hSupport : Function.support R ∩ W = W :=
    Set.inter_eq_right.mpr (fun t ht => (hPos t ht).ne')
  have hVol : 0 < volume W := by
    unfold W
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    linarith
  have hRealIntegral : 0 < ∫ t in W, R t :=
    (setIntegral_pos_iff_support_of_nonneg_ae hR₊ hR).mpr (by rwa [hSupport])
  have hNative : (∫ t in W, G t) = crossHeightTestPairing q T := by
    unfold crossHeightTestPairing
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have ht' : |t| < T := abs_lt.mpr ht
    change (Real.exp (-t) : ℂ) * firstCrossCutoffCoefficient q t =
      (Real.exp (-t) : ℂ) * crossCutoffFourierAtLogHeight q t
    rw [cutoff_fourier_eq_first hq t (hW t ht').1]
  have hRI := integral_re hZI
  change (∫ t in W, R t) = (∫ t in W, z * G t).re at hRI
  rw [integral_const_mul, hNative] at hRI
  refine ⟨q, T, hqLo, hqHi, hT, ?_⟩
  intro hZero
  rw [hZero, mul_zero, Complex.zero_re] at hRI
  exact hRealIntegral.ne' hRI

end
end ManuscriptAudit.Paper8OddCrossWindowPairing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossWindowPairing.exists_nonzero_crossHeightTestPairing
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
