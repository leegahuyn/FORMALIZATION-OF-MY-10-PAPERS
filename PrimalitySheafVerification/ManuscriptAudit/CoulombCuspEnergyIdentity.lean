import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimalitySheafVerification.ManuscriptAudit.CoulombNegativeQuotientForm

/-! Integrated covariant and exterior energy on the actual compact horizontal cusp tests. -/

namespace ManuscriptAudit.CoulombCuspEnergyIdentity

open Filter MeasureTheory Set
open CoulombScaledCuspForms CoulombScaledCuspIntegrals CoulombNegativeQuotientForm
open GammaTwoQuotientHeightIntegral
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped ContDiff Topology UpperHalfPlane

noncomputable section

def exteriorCoefficient (r x y : ℝ) : ℝ :=
  deriv (fun t => (oneForm r t y).2) x - deriv (fun t => (oneForm r x t).1) y

theorem exteriorCoefficient_eq (r x y : ℝ) :
    exteriorCoefficient r x y = -deriv (amplitude r) y := by
  simp [exteriorCoefficient, oneForm]

def exteriorDensity (r y : ℝ) : ℝ := (y * deriv (amplitude r) y)^2

def exteriorEnergy (r : ℝ) : ℝ := 2 * ∫ y : ℝ in (1 : ℝ)..6, exteriorDensity r y

def exteriorEnergyOnQuotient (D : GammaTwoFundamentalDomain) (r : ℝ) : ℝ :=
  ∫ q, quotientHeight q ^ 2 * exteriorDensity r (quotientHeight q) ∂D.quotientMeasure

theorem exterior_density_high (r : ℝ) (z : ℍ) (hz : 1 ≤ z.im) :
    quotientHeight (gammaTwoQuotientMk z) ^ 2 *
        exteriorDensity r (quotientHeight (gammaTwoQuotientMk z)) =
      z.im ^ 4 * exteriorCoefficient r z.re z.im ^ 2 := by
  rw [quotientHeight_high z hz, exteriorDensity, exteriorCoefficient_eq]
  ring

private theorem derivative_continuous (r : ℝ) : Continuous (deriv (amplitude r)) :=
  (contDiff_infty.mp (amplitude_smooth r) 1).continuous_deriv_one

private theorem exteriorDensity_zero (r y : ℝ) (hr : 1 ≤ r) (hy : y ≤ 1 ∨ 6 ≤ y) :
    exteriorDensity r y = 0 := by
  have he : amplitude r =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
    rcases hy with hy | hy
    · filter_upwards [Iio_mem_nhds (show y < 2 by linarith)] with z hz
      exact amplitude_zero r z hr (Or.inl hz.le)
    · filter_upwards [Ioi_mem_nhds (show 5 < y by linarith)] with z hz
      exact amplitude_zero r z hr (Or.inr hz.le)
  simp [exteriorDensity, he.deriv_eq]

theorem exterior_energy_on_quotient_eq
    (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) :
    exteriorEnergyOnQuotient D r = exteriorEnergy r := by
  have hd : Continuous (exteriorDensity r) :=
    (continuous_id.mul (derivative_continuous r)).pow 2
  unfold exteriorEnergyOnQuotient exteriorEnergy
  rw [integral_profile D (exteriorDensity r) hd.measurable
      (fun y hy => exteriorDensity_zero r y hr (Or.inl hy)),
    setIntegral_eq_interval _ (by norm_num : (1 : ℝ) ≤ 6)
      (fun y hy => exteriorDensity_zero r y hr (Or.inr (le_of_lt hy)))] <;> rfl

theorem covariant_eq_mass_add_exterior (r : ℝ) (hr : 1 ≤ r) :
    energy r = mass r + exteriorEnergy r := by
  let a := amplitude r
  let b := fun y : ℝ => a y^2 + 2*y*a y*deriv a y
  have ha := (amplitude_smooth r).continuous
  have hd := derivative_continuous r
  have hb : Continuous b := (ha.pow 2).add
    (((continuous_const.mul continuous_id).mul ha).mul hd)
  have hA : Differentiable ℝ a :=
    (contDiff_infty.mp (amplitude_smooth r) 1).differentiable (by decide)
  have hder (y : ℝ) : HasDerivAt (fun z : ℝ => z*a z^2) (b y) y := by
    have hAy : HasDerivAt a (deriv a y) y := (hA y).hasDerivAt
    have hSq : HasDerivAt (fun z : ℝ => a z^2) (2*a y*deriv a y) y := by
      have hMul := HasDerivAt.fun_mul hAy hAy
      have hValue : deriv a y*a y + a y*deriv a y = 2*a y*deriv a y := by ring
      rw [hValue] at hMul
      simpa only [pow_two] using hMul
    have hProd : HasDerivAt (fun z : ℝ => z*a z^2)
        (1*a y^2 + y*(2*a y*deriv a y)) y :=
      HasDerivAt.fun_mul (hasDerivAt_id y) hSq
    have hValue : 1*a y^2 + y*(2*a y*deriv a y) = b y := by
      dsimp only [b]
      ring
    rw [hValue] at hProd
    exact hProd
  have hz : (∫ y : ℝ in (1 : ℝ)..6, b y) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y)
      (hb.intervalIntegrable (μ := (volume : Measure ℝ)) 1 6)]
    have hL : amplitude r 1 = 0 := amplitude_zero r 1 hr (Or.inl (by norm_num))
    have hR : amplitude r 6 = 0 := amplitude_zero r 6 hr (Or.inr (by norm_num))
    simp [a,hL,hR]
  have hpoint (y : ℝ) : a y^2 + (y * deriv a y + a y)^2 =
      (a y^2 + exteriorDensity r y) + b y := by
    dsimp [a,b,exteriorDensity]
    ring
  have hm : IntervalIntegrable (fun y : ℝ => amplitude r y^2) volume 1 6 :=
    (ha.pow 2).intervalIntegrable 1 6
  have he : IntervalIntegrable (exteriorDensity r) volume 1 6 :=
    ((continuous_id.mul hd).pow 2).intervalIntegrable 1 6
  unfold energy mass exteriorEnergy
  simp_rw [show ∀ y, amplitude r y^2 + (y * deriv (amplitude r) y + amplitude r y)^2 =
      (amplitude r y^2 + exteriorDensity r y) + b y from hpoint]
  rw [intervalIntegral.integral_add (hm.add he) (hb.intervalIntegrable 1 6),
    intervalIntegral.integral_add hm he, hz]
  ring

theorem actual_coclosed_cusp_energy_identity
    (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) :
    energyOnQuotient D r = massOnQuotient D r + exteriorEnergyOnQuotient D r := by
  rw [energyOnQuotient_eq D r hr, massOnQuotient_eq D r hr,
    exterior_energy_on_quotient_eq D r hr, covariant_eq_mass_add_exterior r hr]

end
end ManuscriptAudit.CoulombCuspEnergyIdentity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombCuspEnergyIdentity.exteriorCoefficient_eq,
      ``ManuscriptAudit.CoulombCuspEnergyIdentity.exterior_density_high,
      ``ManuscriptAudit.CoulombCuspEnergyIdentity.exterior_energy_on_quotient_eq,
      ``ManuscriptAudit.CoulombCuspEnergyIdentity.covariant_eq_mass_add_exterior,
      ``ManuscriptAudit.CoulombCuspEnergyIdentity.actual_coclosed_cusp_energy_identity] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
