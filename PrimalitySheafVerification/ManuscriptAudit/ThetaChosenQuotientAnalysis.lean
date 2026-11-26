import Lean.Util.CollectAxioms
import PrimalitySheafVerification.Mock2_FunctionalAnalysis
import PrimalitySheafVerification.ManuscriptAudit.ThetaGlobalSection
import PrimalitySheafVerification.ManuscriptAudit.ThetaLevelTwoTiles

/-! The finite square mass of the theta section on the repository's measured level-two quotient. -/

namespace ManuscriptAudit.ThetaChosenQuotientAnalysis

open MeasureTheory Set
open Mock2FA.GammaTwoQuotientGeometry
open ThetaProfileGenerators ThetaGammaTwoMetric ThetaGlobalSection ThetaLevelTwoTiles
open scoped UpperHalfPlane Pointwise MatrixGroups

noncomputable section

private theorem invariant_density (g : GammaTwoEffective) (z : ℍ) :
    thetaDensity jacobiTheta (g • z) = thetaDensity jacobiTheta z := by
  obtain ⟨γ, rfl⟩ := effective_exists_gamma g
  rw [gammaTwoEffectiveElement_smul]
  exact thetaDensity_invariant (γ : SL(2, ℤ)) γ.property z

private theorem density_continuous : Continuous (thetaDensity jacobiTheta) := by
  have h : Continuous (fun z : ℍ => jacobiTheta (z : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    exact ContinuousAt.comp' (f := UpperHalfPlane.coe) (x := z)
      (continuousAt_jacobiTheta z.im_pos) UpperHalfPlane.continuous_coe.continuousAt
  exact (Real.continuous_sqrt.comp UpperHalfPlane.continuous_im).mul (h.norm.pow 2)

theorem weightedDensity_integrableOn_chosenDomain :
    IntegrableOn (thetaDensity jacobiTheta) chosenGammaTwoFundamentalDomain.carrier
      hyperbolicMeasure := by
  have hOpen : IntegrableOn (thetaDensity jacobiTheta) gammaTwoOpenCarrier hyperbolicMeasure := by
    rw [gammaTwoOpenCarrier]
    apply integrableOn_iUnion_of_summable_integral_norm
    · intro q
      apply (thetaDensity_integrableOn_translate (gammaTwoCosetRep q)).mono_set
      rintro z ⟨w, hw, rfl⟩
      exact Set.mem_smul_set.mpr ⟨w, ModularGroup.fdo_subset_fd hw, rfl⟩
    · exact Summable.of_finite
  exact hOpen.congr_set_ae gammaTwoOpenCarrier_closure_ae_eq.symm

def quotientDensity : GammaTwoQuotient → ℝ :=
  descendInvariant (thetaDensity jacobiTheta) invariant_density

theorem quotientDensity_pullback (z : ℍ) :
    quotientDensity (gammaTwoQuotientMk z) = ‖thetaWeightedMode z‖ ^ (2 : ℕ) :=
  (descendInvariant_mk _ _ z).trans (thetaWeightedMode_norm_sq z).symm

theorem quotientDensity_integrable (D : GammaTwoFundamentalDomain) :
    Integrable quotientDensity D.quotientMeasure := by
  have hd : Measurable quotientDensity :=
    measurable_descendInvariant _ _ density_continuous.measurable
  have hOrbit : AEMeasurable gammaTwoQuotientMk (hyperbolicMeasure.restrict D.carrier) :=
    measurable_quotient_mk''.aemeasurable
  have hI := (chosenGammaTwoFundamentalDomain.integrableOn_iff D
    (thetaDensity jacobiTheta) invariant_density).mp weightedDensity_integrableOn_chosenDomain
  apply (integrable_map_measure hd.aestronglyMeasurable hOrbit).mpr
  simpa only [Function.comp_def, quotientDensity, descendInvariant_mk] using hI

theorem quotientDensity_integral_pos (D : GammaTwoFundamentalDomain) :
    0 < ∫ q, quotientDensity q ∂D.quotientMeasure := by
  have hpos (q : GammaTwoQuotient) : 0 < quotientDensity q := by
    refine Quotient.inductionOn' q fun z => ?_
    change 0 < quotientDensity (gammaTwoQuotientMk z)
    rw [quotientDensity_pullback]
    exact pow_pos (norm_pos_iff.mpr (thetaWeightedMode_ne_zero z)) _
  have hs : Function.support quotientDensity = Set.univ :=
    Set.eq_univ_of_forall fun q => ne_of_gt (hpos q)
  apply (integral_pos_iff_support_of_nonneg (fun q => (hpos q).le)
    (quotientDensity_integrable D)).mpr
  rw [hs]
  exact isOpen_univ.measure_pos _ ⟨gammaTwoQuotientMk (⟨Complex.I, by simp⟩ : ℍ), Set.mem_univ _⟩

theorem quotientDensity_integral_domain_independent (D₁ D₂ : GammaTwoFundamentalDomain) :
    (∫ q, quotientDensity q ∂D₁.quotientMeasure) =
      ∫ q, quotientDensity q ∂D₂.quotientMeasure := by
  change (∫ q, descendInvariant (thetaDensity jacobiTheta) invariant_density q
    ∂D₁.quotientMeasure) = ∫ q, descendInvariant (thetaDensity jacobiTheta) invariant_density q
    ∂D₂.quotientMeasure
  rw [D₁.integral_descendInvariant_eq _ _ (quotientDensity_integrable D₁).aestronglyMeasurable,
    D₂.integral_descendInvariant_eq _ _ (quotientDensity_integrable D₂).aestronglyMeasurable]
  exact D₁.setIntegral_eq D₂ _ invariant_density

end
end ManuscriptAudit.ThetaChosenQuotientAnalysis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaChosenQuotientAnalysis.weightedDensity_integrableOn_chosenDomain,
      ``ManuscriptAudit.ThetaChosenQuotientAnalysis.quotientDensity_pullback,
      ``ManuscriptAudit.ThetaChosenQuotientAnalysis.quotientDensity_integrable,
      ``ManuscriptAudit.ThetaChosenQuotientAnalysis.quotientDensity_integral_pos,
      ``ManuscriptAudit.ThetaChosenQuotientAnalysis.quotientDensity_integral_domain_independent] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
