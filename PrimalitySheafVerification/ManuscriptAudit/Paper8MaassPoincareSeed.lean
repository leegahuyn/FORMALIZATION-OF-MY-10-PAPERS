import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareKernel

/-! The actual complex-parameter Poincaré seed satisfies the Maass resolvent recurrence. -/

namespace ManuscriptAudit.Paper8MaassPoincareSeed

open Filter MaassLaplacian Paper8OddCrossPoincareKernel Paper8OddCrossScaledRows
open scoped Topology

noncomputable section

private def frequency (μ : ℝ) : ℂ := (2 : ℂ) * (Real.pi : ℂ) * (μ : ℂ)

private def seedAtom (μ : ℝ) (w : ℂ) : ℂ := Complex.exp ((frequency μ * Complex.I) * w)

def poincareSeed (s : ℂ) (μ : ℝ) (x y : ℝ) : ℂ := (y : ℂ) ^ s * seedAtom μ (complexPoint x y)

theorem poincareSeed_eq_exponential (s : ℂ) (μ x y : ℝ) :
    poincareSeed s μ x y =
      (y : ℂ) ^ s * exponentialPhase ((μ : ℂ) * complexPoint x y) := by
  unfold poincareSeed seedAtom exponentialPhase frequency
  congr 2
  ring

private theorem hasDerivAt_seedAtom (μ : ℝ) (w : ℂ) :
    HasDerivAt (seedAtom μ) ((frequency μ * Complex.I) * seedAtom μ w) w := by
  let K := frequency μ * Complex.I
  have hLin : HasDerivAt (fun z : ℂ => K * z) K w := by
    simpa only [id_eq, mul_one, one_mul] using (hasDerivAt_id w).const_mul K
  have h := (Complex.hasDerivAt_exp (K * w)).comp w hLin
  change HasDerivAt (seedAtom μ) (seedAtom μ w * K) w at h
  change HasDerivAt (seedAtom μ) (K * seedAtom μ w) w
  rwa [mul_comm]

private theorem hasDerivAt_yPower (s : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ s) (s * (y : ℂ) ^ (s - 1)) y := by
  by_cases h : s = 0
  · subst s
    simpa only [Complex.cpow_zero, zero_mul] using (hasDerivAt_const y (1 : ℂ))
  · exact hasDerivAt_ofReal_cpow_const hy.ne' h

private theorem height_shift (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * (y : ℂ) ^ (s - 1) = (y : ℂ) ^ s := by
  have h0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  calc
    _ = (y : ℂ) ^ (1 : ℂ) * (y : ℂ) ^ (s - 1) := by rw [Complex.cpow_one]
    _ = (y : ℂ) ^ (1 + (s - 1)) := (Complex.cpow_add _ _ h0).symm
    _ = _ := by congr 1; ring

theorem delta_poincareSeed (s : ℂ) (k μ x y : ℝ) (hy : 0 < y) :
    maassDelta k (poincareSeed s μ) x y =
      s * (1 - s) * poincareSeed s μ x y +
        (4 * (Real.pi : ℂ) * (μ : ℂ)) * (s - (k : ℂ) / 2) * poincareSeed (s + 1) μ x y := by
  let a := frequency μ
  let K := a * Complex.I
  let E (t : ℝ) := seedAtom μ (complexPoint x t)
  let A (t : ℝ) := (t : ℂ) ^ s
  let B (t : ℝ) := (t : ℂ) ^ (s - 1)
  let C (t : ℝ) := (t : ℂ) ^ ((s - 1) - 1)
  have hI : Complex.I * K = -a := by
    unfold K
    calc
      _ = a * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hK2 : K ^ 2 = -(a ^ 2) := by
    unfold K
    rw [mul_pow, pow_two Complex.I, Complex.I_mul_I, mul_neg, mul_one]
  have hEx (t : ℝ) :
      HasDerivAt (fun u : ℝ => seedAtom μ (complexPoint u y)) (K * seedAtom μ (complexPoint t y)) t :=
    horizontal_derivative (hasDerivAt_seedAtom μ (complexPoint t y))
  have hEy (t : ℝ) : HasDerivAt E (-a * E t) t := by
    have h := vertical_derivative (hasDerivAt_seedAtom μ (complexPoint x t))
    change HasDerivAt E (Complex.I * (K * E t)) t at h
    rwa [← mul_assoc, hI] at h
  have hX (t : ℝ) : partialX (poincareSeed s μ) t y = K * (A y * seedAtom μ (complexPoint t y)) := by
    have h := ((hEx t).const_mul (A y)).deriv
    change partialX (poincareSeed s μ) t y = A y * (K * seedAtom μ (complexPoint t y)) at h
    rw [h]
    ring
  have hXX : partialX (partialX (poincareSeed s μ)) x y = K ^ 2 * A y * E y := by
    change deriv (fun t => partialX (poincareSeed s μ) t y) x = _
    rw [funext hX]
    rw [(((hEx x).const_mul (A y)).const_mul K).deriv]
    change K * (A y * (K * E y)) = _
    ring
  have hY (t : ℝ) (ht : 0 < t) :
      partialY (poincareSeed s μ) x t = (s * B t - a * A t) * E t := by
    have h := ((hasDerivAt_yPower s ht).mul (hEy t)).deriv
    change partialY (poincareSeed s μ) x t = (s * B t) * E t + A t * (-a * E t) at h
    rw [h]
    ring
  have hYevent : (partialY (poincareSeed s μ) x) =ᶠ[𝓝 y] (fun t => (s * B t - a * A t) * E t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact hY t ht
  have hYY : partialY (partialY (poincareSeed s μ)) x y =
      (s * (s - 1) * C y - 2 * a * s * B y + a ^ 2 * A y) * E y := by
    change deriv (partialY (poincareSeed s μ) x) y = _
    rw [hYevent.deriv_eq]
    have h := ((((hasDerivAt_yPower (s - 1) hy).const_mul s).sub
      ((hasDerivAt_yPower s hy).const_mul a)).mul (hEy y)).deriv
    change deriv (fun t => (s * B t - a * A t) * E t) y =
      (s * ((s - 1) * C y) - a * (s * B y)) * E y + (s * B y - a * A y) * (-a * E y) at h
    rw [h]
    ring
  let Y : ℂ := y
  have hA : Y * B y = A y := height_shift s hy
  have hB : Y * C y = B y := height_shift (s - 1) hy
  have hC : Y ^ 2 * C y = A y := by
    rw [pow_two, mul_assoc, hB, hA]
  have hD : Y ^ 2 * B y = Y * A y := by
    rw [pow_two, mul_assoc, hA]
  have hPlus : (y : ℂ) ^ (s + 1) = Y * A y := by
    have h0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [Complex.cpow_add _ _ h0, Complex.cpow_one]
    exact mul_comm _ _
  unfold maassDelta
  rw [hXX, hYY, hX, hK2]
  change -(Y ^ 2) * (-(a ^ 2) * A y * E y +
    (s * (s - 1) * C y - 2 * a * s * B y + a ^ 2 * A y) * E y) +
    Complex.I * (k : ℂ) * Y * (K * (A y * E y)) = _
  have hDrift : Complex.I * (k : ℂ) * Y * (K * (A y * E y)) =
      -(k : ℂ) * a * (Y * A y) * E y := by
    calc
      _ = Complex.I * K * ((k : ℂ) * Y * A y * E y) := by ring
      _ = _ := by rw [hI]; ring
  rw [hDrift]
  calc
    _ = (-s * (s - 1) * (Y ^ 2 * C y) + 2 * a * s * (Y ^ 2 * B y) -
        (k : ℂ) * a * (Y * A y)) * E y := by ring
    _ = _ := by
      rw [hC, hD]
      unfold poincareSeed
      rw [hPlus]
      dsimp only [a, frequency, A, E]
      ring

theorem delta_oddInfinitySeed (s : ℂ) (x y : ℝ) (hy : 0 < y) :
    maassDelta (-1 / 2) (poincareSeed s oddInfinityFrequency) x y -
      s * (1 - s) * poincareSeed s oddInfinityFrequency x y =
      (4 * (Real.pi : ℂ) * (oddInfinityFrequency : ℂ)) * (s + 1 / 4) *
        poincareSeed (s + 1) oddInfinityFrequency x y := by
  rw [delta_poincareSeed s (-1 / 2) oddInfinityFrequency x y hy]
  push_cast
  ring

end
end ManuscriptAudit.Paper8MaassPoincareSeed

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassPoincareSeed.delta_oddInfinitySeed
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
