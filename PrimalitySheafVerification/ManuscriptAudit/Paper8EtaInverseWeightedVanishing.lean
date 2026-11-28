import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaInverseCuspVanishing
import PrimalitySheafVerification.ManuscriptAudit.HolomorphicStripPointwise
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspRows

/-!
# Vanishing of the level-four holomorphic spectral partner

The inverse multiplier governs the conjugate holomorphic partner of the
odd weight-negative-one-half problem. The native character at level four
squares to one. Weighted square integrability of the true half-weight
cusp translates yields the polynomial growth required for vanishing.
-/

namespace ManuscriptAudit.Paper8EtaInverseWeightedVanishing

open Set Filter Function MeasureTheory UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8EtaRatioCuspLimit
open Paper8EtaNormalizedCuspTranslate Paper8EtaInverseMultiplier HolomorphicStripEnergy
open Paper8OddCrossCuspRows (levelCharacter)
open scoped MatrixGroups Manifold Topology

theorem conjugate_squaredMultiplier_eq_inv (g : SL(2, ℤ)) :
    (starRingEnd ℂ) (squaredMultiplier g) = (squaredMultiplier g)⁻¹ := by
  have hn : ‖squaredMultiplier g‖ ^ (12 : ℕ) = 1 := by
    simpa only [norm_pow, norm_one] using
      congrArg (fun v : ℂ => ‖v‖) (squaredMultiplier_pow_twelve g)
  have hone : ‖squaredMultiplier g‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (12 : ℕ) ≠ 0)).mp
      (hn.trans (one_pow _).symm)
  have hConj : (starRingEnd ℂ) (squaredMultiplier g) * squaredMultiplier g = 1 := by
    simpa only [hone, Complex.ofReal_one, one_pow] using Complex.conj_mul' (squaredMultiplier g)
  calc
    _ = ((starRingEnd ℂ) (squaredMultiplier g) * squaredMultiplier g) *
        (squaredMultiplier g)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (squaredMultiplier_ne_zero g), mul_one]
    _ = _ := by rw [hConj, one_mul]

theorem levelCharacter_sq (g : CongruenceSubgroup.Gamma0 4) :
    (levelCharacter g : ℂ) ^ 2 = 1 := by
  have hUnit : levelCharacter g * levelCharacter g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hUnit with h | h
  · norm_num [h.1]
  · norm_num [h.1]

theorem cuspTranslate_norm_sq_periodic {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hF : InverseSquaredAutomorphy H f) (g : SL(2, ℤ)) {w : ℕ}
    (hMem : g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H)
    (y : ℝ) (hy : 0 < y) :
    Periodic (fun x : ℝ => ‖cuspTranslate f g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) (w : ℝ) := by
  intro x
  let v (t : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hAdd : v (x + (w : ℝ)) = v x + ((w : ℝ) : ℂ) := by
    simp only [v, Complex.ofReal_add]
    ring
  have hz : 0 < (v x).im := by simpa [v, Complex.mul_im] using hy
  have hz' : 0 < (v x + ((w : ℝ) : ℂ)).im := by simpa using hz
  have hT : ModularGroup.T ^ (w : ℤ) • (⟨v x, hz⟩ : ℍ) =
      ⟨v x + ((w : ℝ) : ℂ), hz'⟩ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]
    apply UpperHalfPlane.ext
    simp [UpperHalfPlane.coe_vadd, add_comm]
  have hD : denominator (ModularGroup.T ^ (w : ℤ)) (⟨v x, hz⟩ : ℍ) = 1 := by
    unfold denominator
    rw [ModularGroup.coe_T_zpow]
    norm_num
  have hEta : ‖ModularForm.eta (ofComplex (v x + ((w : ℝ) : ℂ)) : ℍ)‖ =
      ‖ModularForm.eta (ofComplex (v x) : ℍ)‖ := by
    rw [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz, ← hT, eta_norm_transform, hD]
    simp
  have hAbs (z : ℂ) : ‖weightTwoTranslate f g (ofComplex z)‖ =
      ‖cuspTranslate f g z‖ ^ 2 * ‖ModularForm.eta (ofComplex z : ℍ)‖ ^ 2 := by
    rw [norm_weightTwoTranslate, cuspTranslate, norm_mul, mul_pow]
    ring
  have hPer := congrArg (fun a : ℂ => ‖a‖) (weightTwoTranslate_periodic hF g hMem (v x))
  change ‖weightTwoTranslate f g (ofComplex (v x + ((w : ℝ) : ℂ)))‖ =
    ‖weightTwoTranslate f g (ofComplex (v x))‖ at hPer
  rw [hAbs, hAbs, hEta] at hPer
  change ‖cuspTranslate f g (v (x + w))‖ ^ 2 = ‖cuspTranslate f g (v x)‖ ^ 2
  rw [hAdd]
  exact mul_right_cancel₀
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (ModularForm.eta_ne_zero (ofComplex (v x)).im_pos))) hPer

theorem gammaZero_eq_zero_of_weighted_LTwo {N : ℕ} (hN : 0 < N) (hN6 : N < 6)
    {f : ℍ → ℂ} (hF : InverseSquaredAutomorphy (CongruenceSubgroup.Gamma0 N) f)
    (hHol : MDiff f)
    (hLTwo : ∀ g : SL(2, ℤ),
      IntegrableOn (weightedEnergy (cuspTranslate f g) (N : ℝ)) (Ioi 1)) :
    ∀ z : ℍ, f z = 0 := by
  apply Paper8EtaInverseCuspVanishing.gammaZero_eq_zero_of_polynomial hN hN6 hF hHol
  intro g
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMem := Paper8EtaCuspWidths.conjugatedTranslation_level N g
  obtain ⟨M, _, hGrowth⟩ := HolomorphicStripPointwise.eventually_norm_le_mul_height
    (cuspTranslate f g) (cuspTranslate_holomorphic hHol g) hNR
    (cuspTranslate_norm_sq_periodic hF g hMem) (hLTwo g)
  refine ⟨1, M, ?_⟩
  filter_upwards [tendsto_coe_atImInfty.eventually hGrowth] with z hz
  have hD : 0 < Real.sqrt ‖denominator g z‖ :=
    Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
  change ‖cuspTranslate f g z‖ ≤ M * z.im at hz
  rw [norm_cuspTranslate, div_le_iff₀ hD] at hz
  simpa only [Real.rpow_one] using hz

theorem levelFour_conjugate_odd_partner_eq_zero {f : ℍ → ℂ}
    (factor : CongruenceSubgroup.Gamma0 4 → ℍ → ℂ)
    (hFactor : ∀ g : CongruenceSubgroup.Gamma0 4, ∀ z : ℍ,
      factor g z ^ 2 = (starRingEnd ℂ) (squaredMultiplier (g : SL(2, ℤ))) *
        denominator (g : SL(2, ℤ)) z)
    (hLaw : ∀ g : CongruenceSubgroup.Gamma0 4, ∀ z : ℍ,
      f ((g : SL(2, ℤ)) • z) = (levelCharacter g : ℂ) * factor g z * f z)
    (hHol : MDiff f)
    (hLTwo : ∀ g : SL(2, ℤ), IntegrableOn (weightedEnergy (cuspTranslate f g) 4) (Ioi 1)) :
    ∀ z : ℍ, f z = 0 := by
  have hInv : InverseSquaredAutomorphy (CongruenceSubgroup.Gamma0 4) f := by
    intro g hg z
    have h := hLaw ⟨g, hg⟩ z
    change f (g • z) = (levelCharacter ⟨g, hg⟩ : ℂ) * factor ⟨g, hg⟩ z * f z at h
    rw [h, mul_pow, mul_pow, levelCharacter_sq, one_mul, hFactor, conjugate_squaredMultiplier_eq_inv]
    ring
  exact gammaZero_eq_zero_of_weighted_LTwo (N := 4) (by decide) (by decide) hInv hHol hLTwo

end ManuscriptAudit.Paper8EtaInverseWeightedVanishing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaInverseWeightedVanishing.conjugate_squaredMultiplier_eq_inv,
      ``ManuscriptAudit.Paper8EtaInverseWeightedVanishing.levelCharacter_sq,
      ``ManuscriptAudit.Paper8EtaInverseWeightedVanishing.cuspTranslate_norm_sq_periodic,
      ``ManuscriptAudit.Paper8EtaInverseWeightedVanishing.gammaZero_eq_zero_of_weighted_LTwo,
      ``ManuscriptAudit.Paper8EtaInverseWeightedVanishing.levelFour_conjugate_odd_partner_eq_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
