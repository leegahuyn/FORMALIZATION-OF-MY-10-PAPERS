import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Exact residuals of dilated smooth waves for the logarithmic cusp operator. -/

namespace ManuscriptAudit.Paper9LogCuspWave

open Complex

noncomputable section

set_option backward.isDefEq.respectTransparency false

def frequency (k : ℝ) : ℂ := (k : ℂ) * I

def phase (k t : ℝ) : ℂ := Complex.exp ((t : ℂ) * frequency k)

def amplitude (b : ℝ → ℝ) (R t : ℝ) : ℂ := (b (t / R) : ℂ)

def trial (b : ℝ → ℝ) (k R t : ℝ) : ℂ := amplitude b R t * phase k t

def trialDeriv (b b' : ℝ → ℝ) (k R t : ℝ) : ℂ :=
  (amplitude b' R t * (R : ℂ)⁻¹ + amplitude b R t * frequency k) * phase k t

def trialSecond (b b' b'' : ℝ → ℝ) (k R t : ℝ) : ℂ :=
  (amplitude b'' R t * (R : ℂ)⁻¹ ^ 2 +
    2 * frequency k * amplitude b' R t * (R : ℂ)⁻¹ +
    frequency k ^ 2 * amplitude b R t) * phase k t

def residual (b' b'' : ℝ → ℝ) (k R t : ℝ) : ℂ :=
  (amplitude b'' R t * (R : ℂ)⁻¹ ^ 2 +
    2 * frequency k * amplitude b' R t * (R : ℂ)⁻¹) * phase k t

private theorem phase_hasDerivAt (k t : ℝ) :
    HasDerivAt (phase k) (phase k t * frequency k) t := by
  have h : HasDerivAt (fun z : ℂ => z * frequency k) (frequency k) (t : ℂ) := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (t : ℂ)).mul_const (frequency k)
  exact h.cexp.comp_ofReal

theorem phase_norm (k t : ℝ) : ‖phase k t‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp [frequency, Complex.mul_re, Complex.mul_im]

private theorem amplitude_hasDerivAt (b b' : ℝ → ℝ) (R t : ℝ)
    (hb : ∀ v, HasDerivAt b (b' v) v) :
    HasDerivAt (amplitude b R) (amplitude b' R t * (R : ℂ)⁻¹) t := by
  have hArg : HasDerivAt (fun v : ℝ => v / R) R⁻¹ t := by
    simpa only [id_eq, div_eq_mul_inv, one_mul] using (hasDerivAt_id t).mul_const R⁻¹
  have h := ((hb (t / R)).comp t hArg).ofReal_comp
  convert h using 1 <;> first
  | rfl
  | funext v; rfl
  | simp only [Function.comp_def, amplitude, Complex.ofReal_mul, Complex.ofReal_inv]

theorem trial_hasDerivAt (b b' : ℝ → ℝ) (k R t : ℝ)
    (hb : ∀ v, HasDerivAt b (b' v) v) :
    HasDerivAt (trial b k R) (trialDeriv b b' k R t) t := by
  have h := (amplitude_hasDerivAt b b' R t hb).mul (phase_hasDerivAt k t)
  convert h using 1 <;> first
  | rfl
  | funext y; rfl
  | unfold trialDeriv; ring

theorem trialDeriv_hasDerivAt (b b' b'' : ℝ → ℝ) (k R t : ℝ)
    (hb : ∀ v, HasDerivAt b (b' v) v) (hb' : ∀ v, HasDerivAt b' (b'' v) v) :
    HasDerivAt (trialDeriv b b' k R) (trialSecond b b' b'' k R t) t := by
  have hA := (amplitude_hasDerivAt b' b'' R t hb').mul_const ((R : ℂ)⁻¹)
  have hB := (amplitude_hasDerivAt b b' R t hb).mul_const (frequency k)
  have h := (hA.add hB).mul (phase_hasDerivAt k t)
  convert h using 1 <;> first
  | rfl
  | funext y; rfl
  | unfold trialSecond; simp only [Pi.add_apply]; ring

theorem shifted_mode_residual (b b' b'' : ℝ → ℝ) (k R t : ℝ)
    (hb : ∀ v, HasDerivAt b (b' v) v) (hb' : ∀ v, HasDerivAt b' (b'' v) v) :
    deriv (deriv (trial b k R)) t - (1 / 4 : ℂ) * trial b k R t -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) * trial b k R t = residual b' b'' k R t := by
  have hD : deriv (trial b k R) = trialDeriv b b' k R :=
    funext (fun v => (trial_hasDerivAt b b' k R v hb).deriv)
  have hF : frequency k ^ 2 = -((k : ℂ) ^ 2) := by
    rw [frequency, mul_pow, pow_two I, Complex.I_mul_I]
    ring
  rw [hD, (trialDeriv_hasDerivAt b b' b'' k R t hb hb').deriv]
  unfold trialSecond residual trial
  rw [hF]
  push_cast
  ring

theorem trial_norm_sq (b : ℝ → ℝ) (k R t : ℝ) :
    ‖trial b k R t‖ ^ (2 : ℕ) = b (t / R) ^ 2 := by
  rw [trial, norm_mul, phase_norm, mul_one, amplitude, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem residual_norm_sq (b' b'' : ℝ → ℝ) (k R t : ℝ) :
    ‖residual b' b'' k R t‖ ^ (2 : ℕ) =
      b'' (t / R) ^ 2 * (R⁻¹) ^ 4 + 4 * k ^ 2 * b' (t / R) ^ 2 * (R⁻¹) ^ 2 := by
  let u : ℝ := b'' (t / R) * (R⁻¹) ^ 2
  let v : ℝ := 2 * k * b' (t / R) * R⁻¹
  have he : amplitude b'' R t * (R : ℂ)⁻¹ ^ 2 +
      2 * frequency k * amplitude b' R t * (R : ℂ)⁻¹ =
      (u : ℂ) + (v : ℂ) * I := by
    simp only [u, v, amplitude, frequency, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_inv, Complex.ofReal_ofNat]
    ring
  rw [residual, norm_mul, phase_norm, mul_one, ← Complex.normSq_eq_norm_sq, he]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  dsimp [u, v]
  ring

end
end ManuscriptAudit.Paper9LogCuspWave

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9LogCuspWave.phase_norm,
      ``ManuscriptAudit.Paper9LogCuspWave.trial_hasDerivAt,
      ``ManuscriptAudit.Paper9LogCuspWave.trialDeriv_hasDerivAt,
      ``ManuscriptAudit.Paper9LogCuspWave.shifted_mode_residual,
      ``ManuscriptAudit.Paper9LogCuspWave.trial_norm_sq,
      ``ManuscriptAudit.Paper9LogCuspWave.residual_norm_sq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
