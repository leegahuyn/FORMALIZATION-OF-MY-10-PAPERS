import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoHighStripMeasure
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspNegative
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspSectionSmooth

/-! Actual squared norms of the compact theta sections on the measured Γ(2) quotient. -/

namespace ManuscriptAudit.Paper9CuspNormOnQuotient

open MeasureTheory Set Paper9HighCuspSection Paper9HighCuspNegative
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open ThetaGlobalSection
open scoped UpperHalfPlane

noncomputable section

private theorem norm_invariant (a : ℝ → ℂ) (g : GammaTwoEffective) (z : ℍ) :
    ‖extendedSection a (g • z)‖ ^ (2 : ℕ) = ‖extendedSection a z‖ ^ (2 : ℕ) := by
  obtain ⟨γ, hγ⟩ := effective_exists_gamma g
  rw [hγ z, extendedSection_equivariant, norm_mul, thetaUnitaryFactor_norm, one_mul]

def normSq (Y : ℝ) : GammaTwoQuotient → ℝ :=
  descendInvariant (fun z => ‖extendedSection (heightAmplitude Y) z‖ ^ (2 : ℕ))
    (norm_invariant (heightAmplitude Y))

theorem normSq_pullback (Y : ℝ) (z : ℍ) :
    normSq Y (gammaTwoQuotientMk z) = ‖extendedSection (heightAmplitude Y) z‖ ^ (2 : ℕ) := by
  rw [normSq, descendInvariant_mk]

theorem normSq_high (Y : ℝ) (z : ℍ) (hz : 1 < z.im) :
    normSq Y (gammaTwoQuotientMk z) = Paper9CuspPotentialForm.heightTest Y z.im ^ 2 := by
  rw [normSq_pullback, extendedSection_at_high _ z hz, heightAmplitude, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem normSq_measurable (Y : ℝ) (hY : 1 ≤ Y) : Measurable (normSq Y) := by
  have h := (extendedSection_realSmooth (heightAmplitude Y) (heightAmplitude_smooth Y)
    Y hY (heightAmplitude_zero Y)).continuousOn
  have hc : Continuous (extendedSection (heightAmplitude Y)) := by
    have he := h.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)
    convert he using 1
    funext z
    change extendedSection (heightAmplitude Y) z =
      extendedSection (heightAmplitude Y) (UpperHalfPlane.ofComplex (z : ℂ))
    rw [UpperHalfPlane.ofComplex_apply]
  exact measurable_descendInvariant _ _ (hc.measurable.norm.pow_const 2)

theorem image_closedStrip_subset_highStrip (Y : ℝ) (hY : 1 ≤ Y) :
    gammaTwoQuotientMk '' closedStrip Y ⊆ gammaTwoQuotientMk '' GammaTwoHighStripMeasure.strip := by
  rintro q ⟨z, hz, rfl⟩
  have hHigh : 1 < z.im := by
    have h := (show z.im ∈ Icc (Y + 2) (Y + 5) from hz.2).1
    linarith
  obtain ⟨w, hw, _⟩ := HighInfinityCusp.existsUnique_high_strip_representative le_rfl z hHigh
  obtain ⟨g, hg⟩ : MulAction.orbitRel GammaTwo ℍ w z := Quotient.exact hw.2.2.2
  refine ⟨w, ⟨hw.1, ⟨hw.2.1, hw.2.2.1⟩⟩, ?_⟩
  rw [← hg, gammaTwoQuotientMk_gamma_smul]

theorem normSq_zero_outside_highStrip (Y : ℝ) (hY : 1 ≤ Y) {q : GammaTwoQuotient}
    (hq : q ∉ gammaTwoQuotientMk '' GammaTwoHighStripMeasure.strip) : normSq Y q = 0 := by
  obtain ⟨z, rfl⟩ := gammaTwoQuotientMk_isOpenQuotientMap.surjective q
  have hn : gammaTwoQuotientMk z ∉ gammaTwoQuotientMk '' closedStrip Y :=
    fun h => hq (image_closedStrip_subset_highStrip Y hY h)
  rw [normSq_pullback, extendedSection_zero_outside_strip (heightAmplitude Y) Y hY
    (heightAmplitude_zero Y) z hn, norm_zero]
  norm_num

end
end ManuscriptAudit.Paper9CuspNormOnQuotient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspNormOnQuotient.normSq_high,
      ``ManuscriptAudit.Paper9CuspNormOnQuotient.normSq_measurable,
      ``ManuscriptAudit.Paper9CuspNormOnQuotient.image_closedStrip_subset_highStrip,
      ``ManuscriptAudit.Paper9CuspNormOnQuotient.normSq_zero_outside_highStrip] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
