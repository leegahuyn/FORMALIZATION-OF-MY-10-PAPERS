import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.Periodic
import PrimalitySheafVerification.ManuscriptAudit.HighInfinityCusp
import PrimalitySheafVerification.ManuscriptAudit.ThetaChosenQuotientAnalysis

/-! Extend height profiles from the high cusp to actual half-weight sections. -/

namespace ManuscriptAudit.Paper9HighCuspSection

open Set ThetaGlobalSection MaassLaplacian
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane MatrixGroups Pointwise

noncomputable section

private def highLift (q : GammaTwoQuotient) : Prop :=
  ∃ z : ℍ, gammaTwoQuotientMk z = q ∧ 1 < z.im

theorem orbitLift {w z : ℍ} (h : gammaTwoQuotientMk w = gammaTwoQuotientMk z) :
    ∃ γ : GammaTwo, γ • z = w := by
  obtain ⟨g, hg⟩ : MulAction.orbitRel GammaTwoEffective ℍ w z := Quotient.exact h
  obtain ⟨γ, hγ⟩ := effective_exists_gamma g
  exact ⟨γ, (hγ z).symm.trans hg⟩

private theorem sameHighHeightAndMode {w z : ℍ} (hw : 1 < w.im) (hz : 1 < z.im)
    (h : gammaTwoQuotientMk w = gammaTwoQuotientMk z) :
    w.im = z.im ∧ thetaWeightedMode w = thetaWeightedMode z := by
  obtain ⟨m, hm⟩ :=
    (HighInfinityCusp.high_orbit_iff_even_translate le_rfl hz hw).mp (orbitLift h)
  have him : w.im = z.im := by
    simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hm
  have hperiod : Function.Periodic jacobiTheta (2 : ℂ) := by
    intro τ
    simpa only [add_comm] using jacobiTheta_two_add τ
  have ht : jacobiTheta (w : ℂ) = jacobiTheta (z : ℂ) := by
    rw [hm]
    simpa only [mul_comm] using hperiod.int_mul m (z : ℂ)
  exact ⟨him, by simp only [thetaWeightedMode, him, ht]⟩

def quotientProfile (a : ℝ → ℂ) (q : GammaTwoQuotient) : ℂ := by
  classical
  exact if h : highLift q then a h.choose.im / thetaWeightedMode h.choose else 0

def extendedSection (a : ℝ → ℂ) (z : ℍ) : ℂ :=
  thetaWeightedMode z * quotientProfile a (gammaTwoQuotientMk z)

theorem profile_formula (a : ℝ → ℂ) (z : ℍ) (hz : 1 < z.im) :
    quotientProfile a (gammaTwoQuotientMk z) = a z.im / thetaWeightedMode z := by
  have h : highLift (gammaTwoQuotientMk z) := ⟨z, rfl, hz⟩
  obtain ⟨hm, ht⟩ := sameHighHeightAndMode h.choose_spec.2 hz h.choose_spec.1
  rw [quotientProfile, dif_pos h, hm, ht]

theorem extendedSection_at_high (a : ℝ → ℂ) (z : ℍ) (hz : 1 < z.im) :
    extendedSection a z = a z.im := by
  rw [extendedSection, profile_formula a z hz, mul_comm]
  exact div_mul_cancel₀ _ (thetaWeightedMode_ne_zero z)

theorem extendedSection_equivariant (a : ℝ → ℂ) (γ : GammaTwo) (z : ℍ) :
    extendedSection a (γ • z) = thetaUnitaryFactor γ z * extendedSection a z := by
  rw [extendedSection, extendedSection, gammaTwoQuotientMk_gamma_smul, thetaWeightedMode_equivariant,
    mul_assoc]

theorem extendedSection_at_translated_high (a : ℝ → ℂ) (γ : GammaTwo) (z : ℍ)
    (hz : 1 < (γ • z : ℍ).im) :
    extendedSection a z =
      thetaWeightedMode z * (a (γ • z : ℍ).im / thetaWeightedMode (γ • z)) := by
  unfold extendedSection
  rw [← gammaTwoQuotientMk_gamma_smul γ z, profile_formula a (γ • z) hz]

def closedStrip (Y : ℝ) : Set ℍ :=
  {z | z.re ∈ Icc (0 : ℝ) 2 ∧ z.im ∈ Icc (Y + 2) (Y + 5)}

theorem closedStrip_compact (Y : ℝ) (hY : 1 ≤ Y) : IsCompact (closedStrip Y) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  let rectangle := Icc (0 : ℝ) 2 ×ˢ Icc (Y + 2) (Y + 5)
  let f : ℝ × ℝ → ℂ := fun a => complexPoint a.1 a.2
  have hf : Continuous f := by unfold f complexPoint; fun_prop
  have eq : ((↑) : ℍ → ℂ) '' closedStrip Y = f '' rectangle := by
    ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(z.re, z.im), hz, ?_⟩
      apply Complex.ext <;> simp [f, complexPoint]
    · rintro ⟨a, ha, rfl⟩
      have hy : 0 < a.2 := by linarith [ha.2.1]
      have him : (f a).im = a.2 := complexPoint_im _ _
      let z : ℍ := ⟨f a, him.symm ▸ hy⟩
      refine ⟨z, ?_, rfl⟩
      have hre : (f a).re = a.1 := by simp [f, complexPoint]
      change (f a).re ∈ Icc (0 : ℝ) 2 ∧ (f a).im ∈ Icc (Y + 2) (Y + 5)
      rwa [hre, him]
  rw [eq]
  exact (isCompact_Icc.prod isCompact_Icc).image hf

private theorem q_mk_eq_of_orbitPoint_eq {u z : ℍ}
    (h : LiteralCuspTruncation.orbitPoint u = LiteralCuspTruncation.orbitPoint z) :
    gammaTwoQuotientMk u = gammaTwoQuotientMk z := by
  obtain ⟨g, hg⟩ : MulAction.orbitRel GammaTwo ℍ u z := Quotient.exact h
  rw [← hg, gammaTwoQuotientMk_gamma_smul]

theorem support_subset_closedStrip_image (a : ℝ → ℂ) (Y : ℝ) (hY : 1 ≤ Y)
    (hs : ∀ y, y < Y + 2 ∨ Y + 5 < y → a y = 0) :
    Function.support (quotientProfile a) ⊆ gammaTwoQuotientMk '' closedStrip Y := by
  intro q hq
  have h : highLift q := by
    by_contra hn
    exact hq (by rw [quotientProfile, dif_neg hn])
  let z := h.choose
  have hqz : gammaTwoQuotientMk z = q := h.choose_spec.1
  have hz : 1 < z.im := h.choose_spec.2
  have hn : a z.im ≠ 0 := by
    intro he
    apply hq
    rw [← hqz, profile_formula a z hz, he, zero_div]
  have hi : z.im ∈ Icc (Y + 2) (Y + 5) :=
    ⟨le_of_not_gt fun h' => hn (hs _ (Or.inl h')),
      le_of_not_gt fun h' => hn (hs _ (Or.inr h'))⟩
  obtain ⟨u, hu, _⟩ := HighInfinityCusp.existsUnique_high_strip_representative le_rfl z hz
  have hqu := (q_mk_eq_of_orbitPoint_eq hu.2.2.2).trans hqz
  have him := (sameHighHeightAndMode hu.1 hz (hqu.trans hqz.symm)).1
  exact ⟨u, ⟨⟨hu.2.1, hu.2.2.1.le⟩, him.symm ▸ hi⟩, hqu⟩

theorem extendedSection_zero_outside_strip (a : ℝ → ℂ) (Y : ℝ) (hY : 1 ≤ Y)
    (hs : ∀ y, y < Y + 2 ∨ Y + 5 < y → a y = 0) (z : ℍ)
    (hz : gammaTwoQuotientMk z ∉ gammaTwoQuotientMk '' closedStrip Y) :
    extendedSection a z = 0 := by
  have hq : quotientProfile a (gammaTwoQuotientMk z) = 0 := by
    by_contra hn
    exact hz (support_subset_closedStrip_image a Y hY hs hn)
  rw [extendedSection, hq, mul_zero]

theorem profile_hasCompactSupport (a : ℝ → ℂ) (Y : ℝ) (hY : 1 ≤ Y)
    (hs : ∀ y, y < Y + 2 ∨ Y + 5 < y → a y = 0) :
    HasCompactSupport (quotientProfile a) := by
  have K : IsCompact (gammaTwoQuotientMk '' closedStrip Y) :=
    (closedStrip_compact Y hY).image gammaTwoQuotientMk_isOpenQuotientMap.continuous
  exact K.of_isClosed_subset isClosed_closure
    (closure_minimal (support_subset_closedStrip_image a Y hY hs) K.isClosed)

end
end ManuscriptAudit.Paper9HighCuspSection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9HighCuspSection.profile_formula,
      ``ManuscriptAudit.Paper9HighCuspSection.extendedSection_at_translated_high,
      ``ManuscriptAudit.Paper9HighCuspSection.extendedSection_zero_outside_strip,
      ``ManuscriptAudit.Paper9HighCuspSection.extendedSection_at_high,
      ``ManuscriptAudit.Paper9HighCuspSection.extendedSection_equivariant,
      ``ManuscriptAudit.Paper9HighCuspSection.closedStrip_compact,
      ``ManuscriptAudit.Paper9HighCuspSection.support_subset_closedStrip_image,
      ``ManuscriptAudit.Paper9HighCuspSection.profile_hasCompactSupport] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
