import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaNormalizedCuspTranslate
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaRatioPolynomialGrowth
import PrimalitySheafVerification.ManuscriptAudit.HolomorphicStripPointwise

/-! Narrow-cusp holomorphic eta rigidity from actual weighted cusp square integrability. -/

namespace ManuscriptAudit.Paper8EtaWeightedCuspRigidity

open Set Filter MeasureTheory UpperHalfPlane
open Paper8EtaRigidity Paper8EtaNormalizedCuspTranslate Paper8ActualEtaSquaredModularity
open HolomorphicStripEnergy
open scoped MatrixGroups Manifold Topology

theorem etaRatio_cusp_limit_of_weighted_LTwo {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hHol : MDiff f)
    (hAgree : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ,
      f (g • z) * ModularForm.eta z = f z * ModularForm.eta (g • z : ℍ))
    (g : SL(2, ℤ)) {w : ℕ} (hw : 0 < w) (hw24 : w < 24)
    (hMem : g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H)
    (hLTwo : IntegrableOn (weightedEnergy (cuspTranslate f g) (w : ℝ)) (Ioi 1)) :
    ∃ L : ℂ, Tendsto (fun z : ℍ => etaRatio f (g • z)) atImInfty (𝓝 L) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  obtain ⟨M, hM, hGrowth⟩ := HolomorphicStripPointwise.eventually_norm_le_mul_height
    (cuspTranslate f g) (cuspTranslate_holomorphic hHol g) hwR
      (cuspTranslate_norm_sq_periodic hAgree g hMem) hLTwo
  have hBound : ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ (M * z.im ^ (1 : ℝ)) * Real.sqrt ‖denominator g z‖ := by
    filter_upwards [tendsto_coe_atImInfty.eventually hGrowth] with z hz
    have hD : 0 < Real.sqrt ‖denominator g z‖ :=
      Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
    change ‖cuspTranslate f g z‖ ≤ M * z.im at hz
    rw [norm_cuspTranslate, div_le_iff₀ hD] at hz
    simpa only [Real.rpow_one] using hz
  exact Paper8EtaRatioPolynomialGrowth.eta_ratio_limit_of_polynomial_growth g hw hw24 hM
    (translate_periodic_of_conjugatedTranslation_mem (etaRatio_invariant hAgree) g hMem)
    (translate_holomorphic (etaRatio_holomorphic hHol) g) hBound

theorem gammaZero_eq_const_mul_eta_of_weighted_LTwo {N : ℕ} (hN : 0 < N) (hN24 : N < 24)
    {f : ℍ → ℂ} (hHol : MDiff f)
    (hAgree : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ,
      f (g • z) * ModularForm.eta z = f z * ModularForm.eta (g • z : ℍ))
    (hLTwo : ∀ g : SL(2, ℤ),
      IntegrableOn (weightedEnergy (cuspTranslate f g) (N : ℝ)) (Ioi 1)) :
    ∃ c : ℂ, ∀ z : ℍ, f z = c * ModularForm.eta z := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hCusp (g : SL(2, ℤ)) : IsBoundedAtImInfty (fun z : ℍ => etaRatio f (g • z)) := by
    obtain ⟨L, hL⟩ := etaRatio_cusp_limit_of_weighted_LTwo hHol hAgree g hN hN24
      (Paper8EtaCuspWidths.conjugatedTranslation_level N g) (hLTwo g)
    exact bounded_of_tendsto hL
  obtain ⟨c, hc⟩ := FiniteIndexWeightZero.weight_zero_eq_const (CongruenceSubgroup.Gamma0 N)
    (etaRatio f) (etaRatio_invariant hAgree) (etaRatio_holomorphic hHol) hCusp
  exact ⟨c, fun z => (div_eq_iff (ModularForm.eta_ne_zero z.im_pos)).1 (congrFun hc z)⟩

end ManuscriptAudit.Paper8EtaWeightedCuspRigidity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaWeightedCuspRigidity.etaRatio_cusp_limit_of_weighted_LTwo,
      ``ManuscriptAudit.Paper8EtaWeightedCuspRigidity.gammaZero_eq_const_mul_eta_of_weighted_LTwo] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
