import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientHeightIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspSection

/-! Arbitrary finite height intervals above one give compact support on the cusp quotient. -/

namespace ManuscriptAudit.Paper9ArbitraryHeightSupport

open Set Paper9HighCuspSection GammaTwoQuotientHeightIntegral
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane Pointwise

noncomputable section

def closedHeightStrip (a b : ℝ) : Set ℍ :=
  {z | z.re ∈ Icc (0 : ℝ) 2 ∧ z.im ∈ Icc a b}

theorem closedHeightStrip_compact {a b : ℝ} (ha : 0 < a) :
    IsCompact (closedHeightStrip a b) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  let rectangle := Icc (0 : ℝ) 2 ×ˢ Icc a b
  let f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hf : Continuous f := by unfold f; fun_prop
  have he : ((↑) : ℍ → ℂ) '' closedHeightStrip a b = f '' rectangle := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(z.re, z.im), hz, ?_⟩
      apply Complex.ext <;> simp [f, Complex.mul_re, Complex.mul_im]
    · rintro ⟨p, hp, rfl⟩
      have him : (f p).im = p.2 := by simp [f, Complex.mul_im]
      have hre : (f p).re = p.1 := by simp [f, Complex.mul_re]
      let z : ℍ := ⟨f p, him.symm ▸ ha.trans_le hp.2.1⟩
      refine ⟨z, ?_, rfl⟩
      change (f p).re ∈ Icc (0 : ℝ) 2 ∧ (f p).im ∈ Icc a b
      rwa [hre, him]
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image hf

theorem support_subset_quotient_strip (u : ℝ → ℂ) {a b : ℝ}
    (hSupport : ∀ y, y < a ∨ b < y → u y = 0) :
    Function.support (quotientProfile u) ⊆ gammaTwoQuotientMk '' closedHeightStrip a b := by
  intro q hq
  have h : ∃ z : ℍ, gammaTwoQuotientMk z = q ∧ 1 < z.im := by
    by_contra hNone
    apply hq
    unfold quotientProfile
    split
    next hExists =>
      exact (hNone (show ∃ z : ℍ, gammaTwoQuotientMk z = q ∧ 1 < z.im from hExists)).elim
    next => rfl
  obtain ⟨z, hqz, hz⟩ := h
  have hNonzero : u z.im ≠ 0 := by
    intro e
    apply hq
    rw [← hqz, profile_formula u z hz, e, zero_div]
  have hi : z.im ∈ Icc a b :=
    ⟨le_of_not_gt fun h' => hNonzero (hSupport _ (Or.inl h')),
      le_of_not_gt fun h' => hNonzero (hSupport _ (Or.inr h'))⟩
  obtain ⟨v, hv, _⟩ := HighInfinityCusp.existsUnique_high_strip_representative le_rfl z hz
  obtain ⟨g, hg⟩ : MulAction.orbitRel GammaTwo ℍ v z := Quotient.exact hv.2.2.2
  have hqv : gammaTwoQuotientMk v = q := by
    rw [← hg, gammaTwoQuotientMk_gamma_smul, hqz]
  have him : v.im = z.im :=
    (quotientHeight_high v hv.1.le).symm.trans
      ((congrArg quotientHeight (hqv.trans hqz.symm)).trans (quotientHeight_high z hz.le))
  exact ⟨v, ⟨⟨hv.2.1, hv.2.2.1.le⟩, him.symm ▸ hi⟩, hqv⟩

theorem profile_compact_support (u : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hSupport : ∀ y, y < a ∨ b < y → u y = 0) :
    HasCompactSupport (quotientProfile u) := by
  have hK : IsCompact (gammaTwoQuotientMk '' closedHeightStrip a b) :=
    (closedHeightStrip_compact ha).image gammaTwoQuotientMk_isOpenQuotientMap.continuous
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (support_subset_quotient_strip u hSupport) hK.isClosed)

end
end ManuscriptAudit.Paper9ArbitraryHeightSupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9ArbitraryHeightSupport.closedHeightStrip_compact,
      ``ManuscriptAudit.Paper9ArbitraryHeightSupport.support_subset_quotient_strip,
      ``ManuscriptAudit.Paper9ArbitraryHeightSupport.profile_compact_support] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
