import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HighInfinityCusp
import PrimalitySheafVerification.ManuscriptAudit.ThetaChosenQuotientAnalysis

/-! An actual locally bounded nonnegative potential on the level-two quotient. -/

namespace ManuscriptAudit.Paper9CuspPotentialGlobal

open MeasureTheory Matrix Set
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open HighInfinityCusp
open scoped UpperHalfPlane MatrixGroups Pointwise

noncomputable section

def orbitHeight (z : ℍ) : ℝ := ⨆ g : GammaTwo, (g • z).im

private theorem height_le (g : GammaTwo) (z : ℍ) :
    (g • z).im ≤ max z.im (1 / z.im) := by
  by_cases hc : (g : SL(2, ℤ)) 1 0 = 0
  · obtain ⟨m, hm⟩ := even_translate_of_bottom_left_zero g z hc
    have him : (g • z).im = z.im := by
      simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hm
    exact him.le.trans (le_max_left _ _)
  · have hsq' : (1 : ℤ) ≤ ((g : SL(2, ℤ)) 1 0) ^ 2 := by
      have h := sq_pos_of_ne_zero hc
      omega
    have hsq : (1 : ℝ) ≤ (( (g : SL(2, ℤ)) 1 0 : ℤ) : ℝ) ^ 2 := by
      exact_mod_cast hsq'
    have hden : z.im ≤ (( (g : SL(2, ℤ)) 1 0 : ℤ) : ℝ) ^ 2 * z.im := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq z.im_pos.le
    exact (height_le_of_bottom_left_ne_zero (g : SL(2, ℤ)) z hc).trans
      ((one_div_le_one_div_of_le z.im_pos hden).trans (le_max_right _ _))

private theorem range_height_le (z : ℍ) {y : ℝ}
    (hy : y ∈ range (fun g : GammaTwo => (g • z).im)) : y ≤ max z.im (1 / z.im) := by
  obtain ⟨g, hg⟩ := hy
  change (g • z).im = y at hg
  rw [← hg]
  exact height_le g z

private theorem own_height_mem (z : ℍ) :
    z.im ∈ range (fun g : GammaTwo => (g • z).im) :=
  ⟨1, congrArg UpperHalfPlane.im (one_smul GammaTwo z)⟩

theorem orbitHeight_ge_im (z : ℍ) : z.im ≤ orbitHeight z :=
  le_csSup ⟨max z.im (1 / z.im), fun _ hy => range_height_le z hy⟩ (own_height_mem z)

theorem orbitHeight_le_bound (z : ℍ) : orbitHeight z ≤ max z.im (1 / z.im) :=
  csSup_le ⟨z.im, own_height_mem z⟩ (fun _ hy => range_height_le z hy)

theorem orbitHeight_eq_of_high (z : ℍ) (hz : 1 ≤ z.im) :
    orbitHeight z = z.im := by
  apply le_antisymm _ (orbitHeight_ge_im z)
  apply (orbitHeight_le_bound z).trans
  refine max_le le_rfl ?_
  apply (div_le_iff₀ z.im_pos).mpr
  nlinarith

theorem orbitHeight_invariant (δ : GammaTwo) (z : ℍ) :
    orbitHeight (δ • z) = orbitHeight z := by
  change sSup (range (fun g : GammaTwo => (g • (δ • z)).im)) =
    sSup (range (fun g : GammaTwo => (g • z).im))
  congr 1
  ext h
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * δ, congrArg UpperHalfPlane.im (mul_smul g δ z)⟩
  · rintro ⟨g, rfl⟩
    refine ⟨g * δ⁻¹, ?_⟩
    change ((g * δ⁻¹) • (δ • z)).im = (g • z).im
    rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one]

theorem orbitHeight_measurable : Measurable orbitHeight := by
  unfold orbitHeight
  apply Measurable.iSup
  intro g
  have h := (UpperHalfPlane.continuous_im.comp
    (continuous_const_smul (gammaTwoEffectiveElement g))).measurable
  simpa only [Function.comp_def, gammaTwoEffectiveElement_smul] using h

private theorem heightPower_invariant (g : GammaTwoEffective) (z : ℍ) :
    orbitHeight (g • z) ^ 6 = orbitHeight z ^ 6 := by
  obtain ⟨γ, hg⟩ := effective_exists_gamma g
  rw [hg z, orbitHeight_invariant]

def quotientPotential : GammaTwoQuotient → ℝ :=
  descendInvariant (fun z => orbitHeight z ^ 6) heightPower_invariant

theorem quotientPotential_measurable : Measurable quotientPotential :=
  measurable_descendInvariant _ _ (orbitHeight_measurable.pow_const 6)

theorem quotientPotential_at_inf (z : ℍ) (hz : 1 ≤ z.im) :
    quotientPotential (gammaTwoQuotientMk z) = z.im ^ 6 := by
  rw [quotientPotential, descendInvariant_mk, orbitHeight_eq_of_high z hz]

theorem quotientPotential_nonneg (q : GammaTwoQuotient) : 0 ≤ quotientPotential q := by
  refine Quotient.inductionOn' q fun z => ?_
  change 0 ≤ orbitHeight z ^ 6
  positivity

theorem quotientPotential_locally_bounded (q : GammaTwoQuotient) :
    ∃ U : Set GammaTwoQuotient, IsOpen U ∧ q ∈ U ∧
      ∃ C : ℝ, ∀ w ∈ U, 0 ≤ quotientPotential w ∧ quotientPotential w ≤ C := by
  refine Quotient.inductionOn' q fun z => ?_
  let U := {w : ℍ | z.im / 2 < w.im} ∩ {w : ℍ | w.im < z.im + 1}
  have hU : IsOpen U := (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  have hz : z ∈ U := ⟨by dsimp; linarith [z.im_pos], by dsimp; linarith⟩
  let C := max (z.im + 1) (2 / z.im)
  refine ⟨gammaTwoQuotientMk '' U, gammaTwoQuotientMk_isOpenQuotientMap.isOpenMap _ hU,
    ⟨z, hz, rfl⟩, C ^ 6, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨quotientPotential_nonneg _, ?_⟩
  change orbitHeight w ^ 6 ≤ C ^ 6
  apply pow_le_pow_left₀ (w.im_pos.le.trans (orbitHeight_ge_im w)) _ 6
  apply (orbitHeight_le_bound w).trans
  refine max_le (hw.2.le.trans (le_max_left _ _)) ?_
  refine le_trans ?_ (le_max_right _ _)
  have hv : 0 < z.im / 2 := by positivity
  have h := one_div_le_one_div_of_le hv hw.1.le
  convert h using 1 <;> field_simp [z.im_ne_zero]

theorem exists_open_above (B : ℝ) :
    ∃ U : Set GammaTwoQuotient, IsOpen U ∧ U.Nonempty ∧ ∀ q ∈ U, B < quotientPotential q := by
  let Y := max 1 B + 1
  let V : Set ℍ := {w | Y < w.im}
  have hY : 1 < Y := by have h := le_max_left (1 : ℝ) B; dsimp [Y]; linarith
  have hB : B < Y := by have h := le_max_right (1 : ℝ) B; dsimp [Y]; linarith
  have hV : IsOpen V := isOpen_lt continuous_const UpperHalfPlane.continuous_im
  let z : ℍ := ⟨((Y + 1 : ℝ) : ℂ) * Complex.I, by
    simpa using (show 0 < Y + 1 by linarith)⟩
  have hz : z ∈ V := by
    change Y < (((Y + 1 : ℝ) : ℂ) * Complex.I).im
    simpa using (lt_add_of_pos_right Y (show (0 : ℝ) < 1 by norm_num))
  refine ⟨gammaTwoQuotientMk '' V, gammaTwoQuotientMk_isOpenQuotientMap.isOpenMap _ hV,
    ⟨gammaTwoQuotientMk z, z, hz, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have h₁ : 1 ≤ w.im := (hY.trans hw).le
  rw [quotientPotential_at_inf w h₁]
  exact (hB.trans hw).trans_le (by
    simpa only [pow_one] using (pow_le_pow_right₀ h₁ (show 1 ≤ (6 : ℕ) by decide)))

theorem quotientPotential_essentially_unbounded (D : GammaTwoFundamentalDomain) :
    ¬ ∃ B : ℝ, ∀ᵐ q ∂D.quotientMeasure, quotientPotential q ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨U, hU, hne, habove⟩ := exists_open_above B
  have hnull := ae_iff.mp hB
  have hsub : U ⊆ {q | ¬ quotientPotential q ≤ B} := fun q hq => not_le_of_gt (habove q hq)
  exact (ne_of_gt (hU.measure_pos _ hne)) (measure_mono_null hsub hnull)

end
end ManuscriptAudit.Paper9CuspPotentialGlobal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.orbitHeight_ge_im,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.orbitHeight_le_bound,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.orbitHeight_eq_of_high,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.orbitHeight_invariant,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.orbitHeight_measurable,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.quotientPotential_measurable,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.quotientPotential_at_inf,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.quotientPotential_nonneg,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.quotientPotential_locally_bounded,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.exists_open_above,
      ``ManuscriptAudit.Paper9CuspPotentialGlobal.quotientPotential_essentially_unbounded] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
