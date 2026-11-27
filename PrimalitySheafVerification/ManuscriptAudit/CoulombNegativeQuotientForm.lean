import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombNegativeFormUnbounded
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientHeightIntegral

/-!
# The negative Coulomb form on the measured width-two quotient cusp

These are the squared norm densities of the compactly supported horizontal
one-form and its covariant derivative, extended by zero from the actual
cusp chart. The negative differential form has no mass lower bound.
-/

namespace ManuscriptAudit.CoulombNegativeQuotientForm

open Set MeasureTheory
open HyperbolicCuspGaugeTest CoulombScaledCuspForms CoulombScaledCuspIntegrals
open GammaTwoQuotientHeightIntegral
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane Topology

noncomputable section

def massDensity (r y : ℝ) : ℝ := amplitude r y ^ 2

def energyDensity (r y : ℝ) : ℝ :=
  amplitude r y ^ 2 + (y * deriv (amplitude r) y + amplitude r y) ^ 2

def pointMass (r : ℝ) (q : GammaTwoQuotient) : ℝ :=
  quotientHeight q ^ 2 * massDensity r (quotientHeight q)

def pointEnergy (r : ℝ) (q : GammaTwoQuotient) : ℝ :=
  quotientHeight q ^ 2 * energyDensity r (quotientHeight q)

def massOnQuotient (D : GammaTwoFundamentalDomain) (r : ℝ) : ℝ :=
  ∫ q, pointMass r q ∂D.quotientMeasure

def energyOnQuotient (D : GammaTwoFundamentalDomain) (r : ℝ) : ℝ :=
  ∫ q, pointEnergy r q ∂D.quotientMeasure

theorem pointMass_high (r : ℝ) (z : ℍ) (hz : 1 ≤ z.im) :
    pointMass r (gammaTwoQuotientMk z) = z.im ^ 2 * (oneForm r z.re z.im).1 ^ 2 := by
  rw [pointMass, quotientHeight_high z hz]
  rfl

theorem pointEnergy_high (r : ℝ) (z : ℍ) (hz : 1 ≤ z.im) :
    pointEnergy r (gammaTwoQuotientMk z) =
      z.im ^ 4 * ((covariantComponents r z.im).1 ^ 2 + (covariantComponents r z.im).2 ^ 2) := by
  rw [pointEnergy, quotientHeight_high z hz, energyDensity, ← covariant_norm_density r z.im z.im_pos]
  ring

private theorem amplitude_deriv_zero (r y : ℝ) (hr : 1 ≤ r) (h : y < 2 ∨ 5 < y) :
    deriv (amplitude r) y = 0 := by
  have hz : amplitude r =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    rcases h with h | h
    · filter_upwards [Iio_mem_nhds h] with t ht
      exact amplitude_zero r t hr (Or.inl (le_of_lt ht))
    · filter_upwards [Ioi_mem_nhds h] with t ht
      exact amplitude_zero r t hr (Or.inr (le_of_lt ht))
  simpa only [deriv_const] using hz.deriv_eq

private theorem energyDensity_zero (r y : ℝ) (hr : 1 ≤ r) (h : y < 2 ∨ 5 < y) :
    energyDensity r y = 0 := by
  rw [energyDensity, amplitude_zero r y hr (h.imp le_of_lt le_of_lt),
    amplitude_deriv_zero r y hr h]
  ring

private theorem energyDensity_continuous (r : ℝ) : Continuous (energyDensity r) := by
  have hAmp := (amplitude_smooth r).continuous
  have hDeriv := (contDiff_infty.mp (amplitude_smooth r) 1).continuous_deriv_one
  exact (hAmp.pow 2).add (((continuous_id.mul hDeriv).add hAmp).pow 2)

theorem massOnQuotient_eq (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) :
    massOnQuotient D r = mass r := by
  have hmeas : Measurable (massDensity r) := ((amplitude_smooth r).continuous.pow 2).measurable
  have hz (y : ℝ) (h : y ≤ 2 ∨ 5 ≤ y) : massDensity r y = 0 := by
    rw [massDensity, amplitude_zero r y hr h]
    norm_num
  unfold massOnQuotient pointMass mass
  rw [integral_profile D (massDensity r) hmeas (fun y hy => hz y (Or.inl (by linarith))),
    setIntegral_eq_interval _ (by norm_num : (1 : ℝ) ≤ 6)
      (fun y hy => hz y (Or.inr (by linarith)))] <;> rfl

theorem energyOnQuotient_eq (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) :
    energyOnQuotient D r = energy r := by
  unfold energyOnQuotient pointEnergy energy
  rw [integral_profile D (energyDensity r) (energyDensity_continuous r).measurable
      (fun y hy => energyDensity_zero r y hr (Or.inl (by linarith))),
    setIntegral_eq_interval _ (by norm_num : (1 : ℝ) ≤ 6)
      (fun y hy => energyDensity_zero r y hr (Or.inr (by linarith)))] <;> rfl

theorem negative_quotient_form_no_mass_lower_bound (D : GammaTwoFundamentalDomain) (b : ℝ) :
    ∃ r : ℝ, 1 ≤ r ∧ 0 < massOnQuotient D r ∧
      -energyOnQuotient D r < b * massOnQuotient D r := by
  let C := max (-b) 0
  obtain ⟨r, hr, hm, hneg⟩ :=
    CoulombNegativeFormUnbounded.negative_form_no_mass_lower_bound C (le_max_right _ _)
  refine ⟨r, hr, (massOnQuotient_eq D r hr).symm ▸ hm, ?_⟩
  rw [energyOnQuotient_eq D r hr, massOnQuotient_eq D r hr]
  have hb : -C ≤ b := by
    have h := le_max_left (-b) (0 : ℝ)
    linarith
  exact hneg.trans_le (mul_le_mul_of_nonneg_right hb hm.le)

end
end ManuscriptAudit.CoulombNegativeQuotientForm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombNegativeQuotientForm.pointMass_high,
      ``ManuscriptAudit.CoulombNegativeQuotientForm.pointEnergy_high,
      ``ManuscriptAudit.CoulombNegativeQuotientForm.massOnQuotient_eq,
      ``ManuscriptAudit.CoulombNegativeQuotientForm.energyOnQuotient_eq,
      ``ManuscriptAudit.CoulombNegativeQuotientForm.negative_quotient_form_no_mass_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
