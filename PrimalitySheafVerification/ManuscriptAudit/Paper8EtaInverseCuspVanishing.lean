import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaInverseMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaRatioPolynomialGrowth

/-!
# Holomorphic vanishing for the inverse squared eta multiplier at small levels

The periodic weight-two product tends to zero at a cusp under polynomial
growth. Native exponential cusp decay applies to the product. Dividing
its norm by the fourth power of eta still leaves positive cusp order
when the width is below six.
-/

namespace ManuscriptAudit.Paper8EtaInverseCuspVanishing

open Set Filter Function UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8ActualEtaNormCusp
open Paper8EtaNormalizedCuspTranslate Paper8EtaInverseMultiplier
open scoped MatrixGroups Manifold Topology

private theorem periodic_cusp_decay {F : ℍ → ℂ} {w : ℝ} (hw : 0 < w)
    (hHol : MDiff F) (hPer : Periodic (F ∘ ofComplex) w)
    (hZero : Tendsto F atImInfty (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ z : ℍ in atImInfty, ‖F z‖ ≤ C * ‖Periodic.qParam w z‖ := by
  have hPositive : ∀ᶠ z : ℂ in comap Complex.im atTop, 0 < z.im :=
    preimage_mem_comap (Ioi_mem_atTop 0)
  have hHolC : ∀ᶠ z : ℂ in comap Complex.im atTop, DifferentiableAt ℂ (F ∘ ofComplex) z :=
    hPositive.mono (fun z hz => UpperHalfPlane.mdifferentiableAt_iff.mp (hHol ⟨z, hz⟩))
  have hZeroC : ZeroAtFilter (comap Complex.im atTop) (F ∘ ofComplex) :=
    hZero.comp tendsto_comap_im_ofComplex
  obtain ⟨C, hC⟩ := (Periodic.exp_decay_of_zero_at_inf hw hPer hHolC hZeroC).bound
  refine ⟨C, ?_⟩
  filter_upwards [tendsto_coe_atImInfty.eventually hC] with z hz
  simpa only [Function.comp_apply, ofComplex_apply, Periodic.norm_qParam,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hz

private theorem weightTwoTranslate_tendsto_zero {f : ℍ → ℂ} (g : SL(2, ℤ))
    {p M : ℝ}
    (hBound : ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ (M * z.im ^ p) * Real.sqrt ‖denominator g z‖) :
    Tendsto (weightTwoTranslate f g) atImInfty (𝓝 0) := by
  have hT := (Paper8EtaRatioPolynomialGrowth.height_rpow_mul_q_rpow_tendsto_zero
    (w := 24) (d := 2) (by norm_num) (by norm_num) (p * 2)).const_mul (4 * M ^ 2)
  have hT' : Tendsto (fun z : ℍ => (4 * M ^ 2) *
      (z.im ^ (p * 2) * ‖Periodic.qParam 24 z‖ ^ (2 : ℝ))) atImInfty (𝓝 0) := by
    simpa only [mul_zero] using hT
  have hMajor : Tendsto (fun z : ℍ =>
      (M * z.im ^ p) ^ 2 * (2 * ‖Periodic.qParam 24 z‖) ^ 2) atImInfty (𝓝 0) := by
    refine hT'.congr (fun z => ?_)
    have hPow : z.im ^ (p * 2) = (z.im ^ p) ^ (2 : ℕ) :=
      Real.rpow_mul_natCast z.im_pos.le p 2
    rw [hPow, Real.rpow_two]
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg (weightTwoTranslate f g z))) ?_ hMajor
  filter_upwards [hBound, eta_eventual_upper_bound] with z hz hEta
  have hD : 0 < Real.sqrt ‖denominator g z‖ :=
    Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
  have hC : ‖cuspTranslate f g z‖ ≤ M * z.im ^ p := by
    rw [norm_cuspTranslate, div_le_iff₀ hD]
    exact hz
  have hNorm : ‖weightTwoTranslate f g z‖ = ‖cuspTranslate f g z‖ ^ 2 * ‖ModularForm.eta z‖ ^ 2 := by
    rw [norm_weightTwoTranslate, cuspTranslate, ofComplex_apply, norm_mul, mul_pow]
    ring
  rw [hNorm]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hC _)
    (pow_le_pow_left₀ (norm_nonneg _) hEta _) (by positivity) (by positivity)

theorem etaRatio_sq_cusp_zero_of_polynomial {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hF : InverseSquaredAutomorphy H f) (hHol : MDiff f)
    (g : SL(2, ℤ)) {w : ℕ} (hw : 0 < w) (hw6 : w < 6)
    (hMem : g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H)
    {p M : ℝ}
    (hBound : ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ (M * z.im ^ p) * Real.sqrt ‖denominator g z‖) :
    Tendsto (fun z : ℍ => etaRatio f (g • z) ^ 2) atImInfty (𝓝 0) := by
  let α : ℝ := (w : ℝ) / 6
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hw6R : (w : ℝ) < 6 := by exact_mod_cast hw6
  have hd : 0 < 1 - α := by dsimp [α]; linarith
  obtain ⟨C, hC⟩ := periodic_cusp_decay hwR (weightTwoTranslate_holomorphic hHol g)
    (weightTwoTranslate_periodic hF g hMem) (weightTwoTranslate_tendsto_zero g hBound)
  have hQ := (Periodic.qParam_tendsto_atImInfty hwR).norm
  have hQ' : Tendsto (fun z : ℍ => ‖Periodic.qParam (w : ℝ) z‖) atImInfty (𝓝 0) := by
    simpa only [norm_zero] using hQ
  have hT : Tendsto (fun z : ℍ => (16 * C) * ‖Periodic.qParam (w : ℝ) z‖ ^ (1 - α))
      atImInfty (𝓝 0) := by
    simpa only [mul_zero] using (hQ'.rpow_const_nhds_zero hd).const_mul (16 * C)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg (etaRatio f (g • z) ^ 2))) ?_ hT
  filter_upwards [hC, eta_eventual_lower_bound hw] with z hProd hEta
  let q : ℝ := ‖Periodic.qParam (w : ℝ) z‖
  have hq : 0 < q := norm_pos_iff.mpr (Periodic.qParam_ne_zero _)
  have hLower : (1 / 16 : ℝ) * q ^ α ≤ ‖ModularForm.eta z‖ ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (1 / 2 : ℝ) * q ^ ((w : ℝ) / 24)) hEta 4
    rw [mul_pow, ← Real.rpow_mul_natCast hq.le] at h
    have hExp : (w : ℝ) / 24 * (4 : ℕ) = α := by unfold α; push_cast; ring
    rw [hExp] at h
    norm_num at h ⊢
    exact h
  have hPositive : 0 < (1 / 16 : ℝ) * q ^ α := mul_pos (by norm_num) (Real.rpow_pos_of_pos hq _)
  rw [norm_weightTwoTranslate] at hProd
  rw [norm_pow]
  change ‖etaRatio f (g • z)‖ ^ 2 ≤ (16 * C) * q ^ (1 - α)
  calc
    _ ≤ (C * q) / ((1 / 16 : ℝ) * q ^ α) := by
      apply (le_div_iff₀ hPositive).2
      exact (mul_le_mul_of_nonneg_left hLower (by positivity)).trans hProd
    _ = _ := by
      rw [Real.rpow_sub hq, Real.rpow_one]
      field_simp [(Real.rpow_pos_of_pos hq α).ne'] <;> ring

theorem eq_zero_of_inverseSquaredAutomorphy_of_polynomial (H : Subgroup SL(2, ℤ))
    [H.FiniteIndex] {f : ℍ → ℂ} (hF : InverseSquaredAutomorphy H f) (hHol : MDiff f)
    (hWidths : ∀ g : SL(2, ℤ), ∃ w : ℕ, 0 < w ∧ w < 6 ∧
      g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H)
    (hGrowth : ∀ g : SL(2, ℤ), ∃ p M : ℝ, ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ (M * z.im ^ p) * Real.sqrt ‖denominator g z‖) :
    ∀ z : ℍ, f z = 0 := by
  let F (z : ℍ) : ℂ := etaRatio f z ^ 24
  have hLim (g : SL(2, ℤ)) : Tendsto (fun z : ℍ => F (g • z)) atImInfty (𝓝 0) := by
    obtain ⟨w, hw, hw6, hMem⟩ := hWidths g
    obtain ⟨p, M, hBound⟩ := hGrowth g
    have h := (etaRatio_sq_cusp_zero_of_polynomial hF hHol g hw hw6 hMem hBound).pow 12
    simpa only [F, ← pow_mul, zero_pow (by decide : (12 : ℕ) ≠ 0)] using h
  obtain ⟨c, hc⟩ := FiniteIndexWeightZero.weight_zero_eq_const H F
    (etaRatio_pow_twentyFour_invariant hF) ((etaRatio_holomorphic hHol).pow 24)
    (fun g => Paper8EtaRigidity.bounded_of_tendsto (hLim g))
  have hFZero : Tendsto F atImInfty (𝓝 0) := by simpa only [one_smul] using hLim 1
  have hFConst : Tendsto F atImInfty (𝓝 c) := by rw [hc]; exact tendsto_const_nhds
  have hc0 : c = 0 := tendsto_nhds_unique hFConst hFZero
  intro z
  by_contra hz
  have hz' : F z = 0 := by simpa only [hc, Function.const_apply, hc0]
  exact (pow_ne_zero _ (div_ne_zero hz (ModularForm.eta_ne_zero z.im_pos))) hz'

theorem gammaZero_eq_zero_of_polynomial {N : ℕ} (hN : 0 < N) (hN6 : N < 6)
    {f : ℍ → ℂ} (hF : InverseSquaredAutomorphy (CongruenceSubgroup.Gamma0 N) f)
    (hHol : MDiff f)
    (hGrowth : ∀ g : SL(2, ℤ), ∃ p M : ℝ, ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ (M * z.im ^ p) * Real.sqrt ‖denominator g z‖) :
    ∀ z : ℍ, f z = 0 := by
  letI : NeZero N := ⟨hN.ne'⟩
  exact eq_zero_of_inverseSquaredAutomorphy_of_polynomial (CongruenceSubgroup.Gamma0 N) hF hHol
    (fun g => ⟨N, hN, hN6, Paper8EtaCuspWidths.conjugatedTranslation_level N g⟩) hGrowth

end ManuscriptAudit.Paper8EtaInverseCuspVanishing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaInverseCuspVanishing.etaRatio_sq_cusp_zero_of_polynomial,
      ``ManuscriptAudit.Paper8EtaInverseCuspVanishing.eq_zero_of_inverseSquaredAutomorphy_of_polynomial,
      ``ManuscriptAudit.Paper8EtaInverseCuspVanishing.gammaZero_eq_zero_of_polynomial] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
