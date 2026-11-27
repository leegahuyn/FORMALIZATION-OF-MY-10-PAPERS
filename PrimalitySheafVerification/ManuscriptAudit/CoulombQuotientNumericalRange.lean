import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombQuotientTestL2
import PrimalitySheafVerification.ManuscriptAudit.SpectralQuarterShift

/-! Paper 10, physical pp. 493–495. The unprojected convention in
Remark 4.12 and the negative differential sign in (4.43) give
expectations unbounded below whenever the native operator domain
contains the compactly supported co-closed tests and realizes their
checked diagonal form. -/

namespace ManuscriptAudit.CoulombQuotientNumericalRange

open MeasureTheory CoulombNegativeQuotientForm CoulombBoundedQuotientPotential
open CoulombQuotientTestL2 SpectralQuarterShift (withPotential)
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Expectations of a partially defined linear operator on its unit vectors. -/
def numericalRange (T : H →ₗ.[ℝ] H) : Set ℝ :=
  {c | ∃ u : T.domain, ‖(u : H)‖ = 1 ∧ inner ℝ (u : H) (T u) = c}

private theorem unit_expectation_lt (T : H →ₗ.[ℝ] H) (v : T.domain) {b : ℝ}
    (hv : 0 < ‖(v : H)‖)
    (hvForm : inner ℝ (v : H) (T v) < b * ‖(v : H)‖ ^ 2) :
    ∃ u : T.domain, ‖(u : H)‖ = 1 ∧ inner ℝ (u : H) (T u) < b := by
  let n := ‖(v : H)‖
  let u : T.domain := n⁻¹ • v
  have hu : (u : H) = n⁻¹ • (v : H) := rfl
  have hTu : T u = n⁻¹ • T v := LinearPMap.map_smul T n⁻¹ v
  refine ⟨u, ?_, ?_⟩
  · rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv)]
    exact inv_mul_cancel₀ hv.ne'
  · calc
      _ = n⁻¹ ^ 2 * inner ℝ (v : H) (T v) := by
        rw [hu, hTu, real_inner_smul_left, real_inner_smul_right]
        ring
      _ = inner ℝ (v : H) (T v) / n ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow, mul_comm]
      _ < b := (div_lt_iff₀ (pow_pos hv 2)).mpr hvForm

private theorem unbounded_of_unit_tests (T : H →ₗ.[ℝ] H)
    (h : ∀ b : ℝ, ∃ u : T.domain, ‖(u : H)‖ = 1 ∧ inner ℝ (u : H) (T u) < b) :
    ¬ BddBelow (numericalRange T) := by
  rintro ⟨b, hb⟩
  obtain ⟨u, hu, hlt⟩ := h b
  have hmem : inner ℝ (u : H) (T u) ∈ numericalRange T := ⟨u, hu, rfl⟩
  exact (not_lt_of_ge (hb hmem)) hlt

private theorem test_norm_pos (v : H) (m : ℝ) (h : ‖v‖ ^ 2 = m) (hm : 0 < m) :
    0 < ‖v‖ := by
  have hnonneg := norm_nonneg v
  nlinarith

/-- Any realization of the literal negative quotient form with a bounded
scalar multiplier on these tests has numerical range unbounded below. -/
theorem numericalRange_unbounded_of_quotient_tests (D : GammaTwoFundamentalDomain)
    (V : GammaTwoQuotient → ℝ) (hV : Measurable V) {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (T : H →ₗ.[ℝ] H) (test : ∀ r : ℝ, 1 ≤ r → T.domain)
    (hMass : ∀ r hr, ‖(test r hr : H)‖ ^ 2 = massOnQuotient D r)
    (hForm : ∀ r hr, inner ℝ (test r hr : H) (T (test r hr)) =
      -energyOnQuotient D r + potentialIntegral D V r) :
    ¬ BddBelow (numericalRange T) := by
  apply unbounded_of_unit_tests
  intro b
  obtain ⟨r, hr, hm, hf⟩ := bounded_potential_form_no_mass_lower_bound D V hV hB b
  apply unit_expectation_lt T (test r hr)
    (test_norm_pos (test r hr : H) (massOnQuotient D r) (hMass r hr) hm)
  rw [hForm r hr, hMass r hr]
  exact hf

/-- The statement applies in the native scalar (L^2) space for the
horizontal coefficients, with no abstract mass comparison hypothesis. -/
theorem quotientL2_numericalRange_unbounded (D : GammaTwoFundamentalDomain)
    (V : GammaTwoQuotient → ℝ) (hV : Measurable V) {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (T : quotientL2 D →ₗ.[ℝ] quotientL2 D)
    (hDomain : ∀ r hr, testVector D r hr ∈ T.domain)
    (hForm : ∀ r hr, inner ℝ (testVector D r hr) (T ⟨testVector D r hr, hDomain r hr⟩) =
      -energyOnQuotient D r + potentialIntegral D V r) :
    ¬ BddBelow (numericalRange T) :=
  numericalRange_unbounded_of_quotient_tests D V hV hB T
    (fun r hr => ⟨testVector D r hr, hDomain r hr⟩) (testVector_norm_sq D) hForm

private theorem potential_expectation_le (W : H →L[ℝ] H) (v : H) :
    inner ℝ v (W v) ≤ ‖W‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖inner ℝ v (W v)‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ ‖v‖ * ‖W v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖W‖ * ‖v‖) := mul_le_mul_of_nonneg_left (W.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

/-- Even an arbitrary bounded operator perturbation cannot create a
lower-bounded numerical range for a negative differential realization
on the same actual quotient tests. -/
theorem bounded_perturbation_numericalRange_unbounded [CompleteSpace H]
    (D : GammaTwoFundamentalDomain) (T : H →ₗ.[ℝ] H) (W : H →L[ℝ] H)
    (test : ∀ r : ℝ, 1 ≤ r → T.domain)
    (hMass : ∀ r hr, ‖(test r hr : H)‖ ^ 2 = massOnQuotient D r)
    (hEnergy : ∀ r hr, inner ℝ (test r hr : H) (T (test r hr)) = -energyOnQuotient D r) :
    ¬ BddBelow (numericalRange (withPotential T W)) := by
  apply unbounded_of_unit_tests
  intro b
  obtain ⟨r, hr, hm, hf⟩ := negative_quotient_form_no_mass_lower_bound D (b - ‖W‖)
  let v := test r hr
  have hv : 0 < ‖(v : H)‖ := test_norm_pos _ _ (hMass r hr) hm
  apply unit_expectation_lt (withPotential T W) v hv
  change inner ℝ (v : H) (W (v : H) + T v) < b * ‖(v : H)‖ ^ 2
  rw [inner_add_right]
  have hP := potential_expectation_le W (v : H)
  have hE : inner ℝ (v : H) (T v) < (b - ‖W‖) * ‖(v : H)‖ ^ 2 := by
    change inner ℝ (test r hr : H) (T (test r hr)) < (b - ‖W‖) * ‖(test r hr : H)‖ ^ 2
    rw [hEnergy r hr, hMass r hr]
    exact hf
  calc
    _ < ‖W‖ * ‖(v : H)‖ ^ 2 + (b - ‖W‖) * ‖(v : H)‖ ^ 2 := by
      exact add_lt_add_of_le_of_lt hP hE
    _ = _ := by ring

end
end ManuscriptAudit.CoulombQuotientNumericalRange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoulombQuotientNumericalRange.numericalRange_unbounded_of_quotient_tests,
      ``ManuscriptAudit.CoulombQuotientNumericalRange.quotientL2_numericalRange_unbounded,
      ``ManuscriptAudit.CoulombQuotientNumericalRange.bounded_perturbation_numericalRange_unbounded] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
