import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCriticalHolomorphic
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaHalfWeightPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaInverseWeightedVanishing

/-!
# From the actual odd Maass raising kernel to vanishing

The level-four odd weight-negative-one-half law uses the native eta
phase and the native lower-right character. After conjugation and
removal of the height factor, the same Maass strip mass is the
weighted holomorphic cusp mass.
-/

namespace ManuscriptAudit.Paper8EtaCriticalOddVanishing

open Set Function MeasureTheory UpperHalfPlane
open MaassLaplacian Paper8NegativeHalfMaassFactorization Paper8MaassCriticalHolomorphic
open Paper8ActualEtaSquaredModularity Paper8EtaHalfWeightPhase Paper8EtaInverseMultiplier
open Paper8EtaNormalizedCuspTranslate HolomorphicStripEnergy
open Paper8EtaInverseWeightedVanishing (conjugate_squaredMultiplier_eq_inv levelCharacter_sq)
open Paper8OddCrossCuspRows (levelCharacter)
open scoped MatrixGroups Manifold

noncomputable section

def OddMaassLaw (F : ℂ → ℂ) : Prop :=
  ∀ g : CongruenceSubgroup.Gamma0 4, ∀ z : ℍ,
    F ((g : SL(2, ℤ)) • z : ℍ) = (levelCharacter g : ℂ) *
      negativePhase (g : SL(2, ℤ)) z * F z

def partnerOnUpper (F : ℂ → ℂ) (z : ℍ) : ℂ := holomorphicPartner F z

def maassStripEnergy (F : ℂ → ℂ) (g : SL(2, ℤ)) (width y : ℝ) : ℝ :=
  (∫ x : ℝ in (0 : ℝ)..width, ‖F (g • ofComplex (complexPoint x y) : ℍ)‖ ^ 2) / y ^ 2

theorem partner_inverseSquaredAutomorphy {F : ℂ → ℂ} (hF : OddMaassLaw F) :
    InverseSquaredAutomorphy (CongruenceSubgroup.Gamma0 4) (partnerOnUpper F) := by
  intro g hg z
  let a (w : ℍ) : ℂ := (w.im ^ (-(1 / 4 : ℝ)) : ℝ)
  let c : ℂ →+* ℂ := starRingEnd ℂ
  let A : CongruenceSubgroup.Gamma0 4 := ⟨g, hg⟩
  have hF' : F (g • z : ℍ) = (levelCharacter A : ℂ) * negativePhase g z * F z := hF A z
  have hHeight : a (g • z) ^ 2 = (‖denominator g z‖ : ℂ) * a z ^ 2 := by
    simpa only [a, Complex.ofReal_pow, Complex.ofReal_mul] using
      congrArg Complex.ofReal (inverse_quarterHeight_sq g z)
  have hChar : c (levelCharacter A : ℂ) ^ 2 = 1 := by
    rw [← map_pow, levelCharacter_sq, map_one]
  have hN : (‖denominator g z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (denominator_ne_zero g z))
  change (a (g • z) * c (F (g • z : ℍ))) ^ 2 =
    (squaredMultiplier g)⁻¹ * (denominator g z * (a z * c (F z)) ^ 2)
  rw [hF']
  simp only [map_mul, mul_pow]
  rw [hHeight, hChar, one_mul, conjugate_negativePhase_sq, conjugate_squaredMultiplier_eq_inv]
  field_simp [hN] <;> ring

theorem partnerOnUpper_holomorphic {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ F z)
    (hKernel : ∀ x y : ℝ, 0 < y → raising (realProfile F) x y = 0) :
    MDiff (partnerOnUpper F) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (partner_differentiableOn hF hKernel).congr ?_
  intro z hz
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, partnerOnUpper]

theorem partner_norm_cuspTranslate_sq (F : ℂ → ℂ) (g : SL(2, ℤ)) (z : ℍ) :
    ‖cuspTranslate (partnerOnUpper F) g z‖ ^ 2 =
      (z.im ^ (-(1 / 4 : ℝ))) ^ (2 : ℕ) * ‖F (g • z : ℍ)‖ ^ 2 := by
  have hN : 0 < ‖denominator g z‖ := norm_pos_iff.mpr (denominator_ne_zero g z)
  have hPos : 0 ≤ (g • z : ℍ).im ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_nonneg (g • z : ℍ).im_pos.le _
  rw [norm_cuspTranslate, div_pow, Real.sq_sqrt hN.le]
  simp only [partnerOnUpper, holomorphicPartner, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hPos, Complex.norm_conj, mul_pow, inverse_quarterHeight_sq]
  field_simp [hN.ne'] <;> ring

theorem partner_weightedEnergy_eq_maassStripEnergy (F : ℂ → ℂ) (g : SL(2, ℤ))
    (width y : ℝ) (hy : 0 < y) :
    weightedEnergy (cuspTranslate (partnerOnUpper F) g) width y =
      maassStripEnergy F g width y := by
  let a : ℝ := (y ^ (-(1 / 4 : ℝ))) ^ (2 : ℕ)
  let G (x : ℝ) : ℝ := ‖F (g • ofComplex (complexPoint x y) : ℍ)‖ ^ 2
  have hNorm (x : ℝ) : ‖cuspTranslate (partnerOnUpper F) g (complexPoint x y)‖ ^ 2 = a * G x := by
    have hIm : 0 < (complexPoint x y).im := by simpa only [complexPoint_im] using hy
    have h := partner_norm_cuspTranslate_sq F g (⟨complexPoint x y, hIm⟩ : ℍ)
    simpa only [a, G, ofComplex_apply_of_im_pos hIm, complexPoint_im] using h
  have hInt :
      (∫ x : ℝ in (0 : ℝ)..width, ‖cuspTranslate (partnerOnUpper F) g (complexPoint x y)‖ ^ 2) =
        a * ∫ x : ℝ in (0 : ℝ)..width, G x := by
    simp only [hNorm, intervalIntegral.integral_const_mul]
  have hExp : a / y ^ (3 / 2 : ℝ) = 1 / y ^ (2 : ℕ) := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast hy.le _ 2, ← Real.rpow_sub hy,
      show (-(1 / 4 : ℝ)) * (2 : ℕ) - 3 / 2 = -(2 : ℝ) by norm_num,
      Real.rpow_neg hy.le, Real.rpow_two, one_div]
  unfold weightedEnergy horizontalEnergy maassStripEnergy
  change (∫ x : ℝ in (0 : ℝ)..width,
      ‖cuspTranslate (partnerOnUpper F) g (complexPoint x y)‖ ^ 2) / y ^ (3 / 2 : ℝ) =
    (∫ x : ℝ in (0 : ℝ)..width, G x) / y ^ (2 : ℕ)
  rw [hInt]
  calc
    _ = (a / y ^ (3 / 2 : ℝ)) * (∫ x : ℝ in (0 : ℝ)..width, G x) := by ring
    _ = _ := by rw [hExp]; ring

theorem odd_maass_raising_kernel_eq_zero {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ F z)
    (hKernel : ∀ x y : ℝ, 0 < y → raising (realProfile F) x y = 0)
    (hMass : ∀ g : SL(2, ℤ), IntegrableOn (maassStripEnergy F g 4) (Ioi 1)) :
    ∀ z : ℍ, F z = 0 := by
  have hPartnerMass (g : SL(2, ℤ)) :
      IntegrableOn (weightedEnergy (cuspTranslate (partnerOnUpper F) g) 4) (Ioi 1) :=
    (hMass g).congr_fun (fun y hy =>
      (partner_weightedEnergy_eq_maassStripEnergy F g 4 (zero_lt_one.trans hy)).symm) measurableSet_Ioi
  have hVanishing := Paper8EtaInverseWeightedVanishing.gammaZero_eq_zero_of_weighted_LTwo
    (N := 4) (by decide) (by decide) (partner_inverseSquaredAutomorphy hLaw)
    (partnerOnUpper_holomorphic hF hKernel) hPartnerMass
  intro z
  by_contra hz
  have hHeight : ((z.im ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos z.im_pos _).ne'
  exact (mul_ne_zero hHeight ((map_ne_zero (starRingEnd ℂ)).2 hz)) (hVanishing z)

end
end ManuscriptAudit.Paper8EtaCriticalOddVanishing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaCriticalOddVanishing.partner_inverseSquaredAutomorphy,
      ``ManuscriptAudit.Paper8EtaCriticalOddVanishing.partnerOnUpper_holomorphic,
      ``ManuscriptAudit.Paper8EtaCriticalOddVanishing.partner_norm_cuspTranslate_sq,
      ``ManuscriptAudit.Paper8EtaCriticalOddVanishing.partner_weightedEnergy_eq_maassStripEnergy,
      ``ManuscriptAudit.Paper8EtaCriticalOddVanishing.odd_maass_raising_kernel_eq_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
