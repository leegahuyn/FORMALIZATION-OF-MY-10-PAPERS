import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoHighStripIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspPotentialGlobal

/-! An exact quotient integral for scalar densities supported high in the infinity cusp. -/

namespace ManuscriptAudit.GammaTwoQuotientHeightIntegral

open MeasureTheory Set Paper9CuspPotentialGlobal
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane

noncomputable section

private theorem height_invariant (g : GammaTwoEffective) (z : ℍ) :
    orbitHeight (g • z) = orbitHeight z := by
  obtain ⟨γ, hg⟩ := effective_exists_gamma g
  rw [hg z, orbitHeight_invariant]

def quotientHeight : GammaTwoQuotient → ℝ := descendInvariant orbitHeight height_invariant

theorem quotientHeight_measurable : Measurable quotientHeight :=
  measurable_descendInvariant _ _ orbitHeight_measurable

theorem quotientHeight_mk (z : ℍ) : quotientHeight (gammaTwoQuotientMk z) = orbitHeight z := by
  rw [quotientHeight, descendInvariant_mk]

theorem quotientHeight_high (z : ℍ) (hz : 1 ≤ z.im) :
    quotientHeight (gammaTwoQuotientMk z) = z.im :=
  (quotientHeight_mk z).trans (orbitHeight_eq_of_high z hz)

theorem mem_strip_image_of_height {q : GammaTwoQuotient} (hq : 1 < quotientHeight q) :
    q ∈ gammaTwoQuotientMk '' GammaTwoHighStripMeasure.strip := by
  obtain ⟨z, rfl⟩ := gammaTwoQuotientMk_isOpenQuotientMap.surjective q
  rw [quotientHeight_mk] at hq
  obtain ⟨γ, hγ⟩ : ∃ γ : GammaTwo, 1 < (γ • z).im := by
    by_contra! hn
    exact (not_lt_of_ge (show orbitHeight z ≤ 1 from ciSup_le hn)) hq
  obtain ⟨w, hw, _⟩ :=
    HighInfinityCusp.existsUnique_high_strip_representative le_rfl (γ • z) hγ
  obtain ⟨g, hg⟩ : MulAction.orbitRel GammaTwo ℍ w (γ • z) :=
    Quotient.exact hw.2.2.2
  refine ⟨w, ⟨hw.1, ⟨hw.2.1, hw.2.2.1⟩⟩, ?_⟩
  calc
    _ = gammaTwoQuotientMk (γ • z) := by rw [← hg, gammaTwoQuotientMk_gamma_smul]
    _ = _ := gammaTwoQuotientMk_gamma_smul _ _

theorem integral_profile (D : GammaTwoFundamentalDomain) (f : ℝ → ℝ) (hf : Measurable f)
    (hzero : ∀ y ≤ 1, f y = 0) :
    (∫ q, quotientHeight q ^ 2 * f (quotientHeight q) ∂D.quotientMeasure) =
      2 * ∫ y in Ioi (1 : ℝ), f y := by
  let A := GammaTwoHighStripMeasure.strip
  let B := gammaTwoQuotientMk '' A
  let F : GammaTwoQuotient → ℝ := fun q => quotientHeight q ^ 2 * f (quotientHeight q)
  have hB : MeasurableSet B :=
    GammaTwoFundamentalDomain.quotientImage_measurable GammaTwoHighStripMeasure.strip_measurable
  have hF : Measurable F :=
    (quotientHeight_measurable.pow_const 2).mul (hf.comp quotientHeight_measurable)
  have hs : (∫ q, F q ∂D.quotientMeasure) = ∫ q in B, F q ∂D.quotientMeasure := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    by_cases hq : q ∈ B
    · rw [indicator_of_mem hq]
    · rw [indicator_of_notMem hq]
      have hq' : quotientHeight q ≤ 1 :=
        le_of_not_gt (fun h => hq (mem_strip_image_of_height h))
      simp only [F, hzero _ hq', mul_zero]
  change (∫ q, F q ∂D.quotientMeasure) = _
  rw [hs]
  change (∫ q, F q ∂(D.quotientMeasure.restrict B)) = _
  rw [← GammaTwoHighStripMeasure.quotient_strip_measure D]
  have hmk : Measurable gammaTwoQuotientMk := measurable_quotient_mk''
  rw [integral_map hmk.aemeasurable hF.aestronglyMeasurable]
  trans ∫ z in A, z.im ^ 2 * f z.im ∂hyperbolicMeasure
  · apply setIntegral_congr_fun GammaTwoHighStripMeasure.strip_measurable
    intro z hz
    change quotientHeight (gammaTwoQuotientMk z) ^ 2 *
      f (quotientHeight (gammaTwoQuotientMk z)) = _
    rw [quotientHeight_high z (show 1 < z.im from hz.1).le]
  · exact GammaTwoHighStripIntegral.height_integral f

theorem setIntegral_eq_interval (f : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b)
    (hzero : ∀ y > b, f y = 0) :
    (∫ y in Ioi (1 : ℝ), f y) = ∫ y : ℝ in (1 : ℝ)..b, f y := by
  rw [intervalIntegral.integral_of_le hb,
    ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  by_cases hlo : 1 < y
  · rw [indicator_of_mem (show y ∈ Ioi (1 : ℝ) from hlo)]
    by_cases hhi : y ≤ b
    · rw [indicator_of_mem (show y ∈ Ioc (1 : ℝ) b from ⟨hlo, hhi⟩)]
    · rw [indicator_of_notMem (fun h : y ∈ Ioc (1 : ℝ) b => hhi h.2),
        hzero y (lt_of_not_ge hhi)]
  · rw [indicator_of_notMem (show y ∉ Ioi (1 : ℝ) from hlo),
      indicator_of_notMem (fun h : y ∈ Ioc (1 : ℝ) b => hlo h.1)]

end
end ManuscriptAudit.GammaTwoQuotientHeightIntegral

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GammaTwoQuotientHeightIntegral.quotientHeight_measurable,
      ``ManuscriptAudit.GammaTwoQuotientHeightIntegral.quotientHeight_high,
      ``ManuscriptAudit.GammaTwoQuotientHeightIntegral.mem_strip_image_of_height,
      ``ManuscriptAudit.GammaTwoQuotientHeightIntegral.integral_profile,
      ``ManuscriptAudit.GammaTwoQuotientHeightIntegral.setIntegral_eq_interval] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
