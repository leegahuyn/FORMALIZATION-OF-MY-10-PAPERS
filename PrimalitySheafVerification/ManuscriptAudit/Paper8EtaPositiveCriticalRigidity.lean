import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaMaassEigenfunction
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaWeightedCuspRigidity
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassGlobalStripEnergy

/-! The actual positive eta Maass lowering kernel is spanned by the native eta function. -/

namespace ManuscriptAudit.Paper8EtaPositiveCriticalRigidity

open Set Function MeasureTheory UpperHalfPlane
open MaassLaplacian Paper8NegativeHalfMaassFactorization Paper8MaassCriticalHolomorphic
open Paper8EtaHalfWeightPhase Paper8EtaMaassEigenfunction
open Paper8EtaCriticalOddVanishing Paper8MaassGlobalStripEnergy
open Paper8EtaCosetMass (cosetCells)
open scoped MatrixGroups Manifold ENNReal

noncomputable section

def lowering (F : Profile) (x y : ℝ) : ℂ :=
  -Complex.I * (y : ℂ) * partialX F x y + (y : ℂ) * partialY F x y - (1 / 4 : ℂ) * F x y

private def conjugate (F : ℂ → ℂ) (z : ℂ) : ℂ := (starRingEnd ℂ) (F z)

private theorem raising_conjugate {F : ℂ → ℂ} {x y : ℝ}
    (hF : DifferentiableAt ℝ F (complexPoint x y)) :
    raising (realProfile (conjugate F)) x y =
      (starRingEnd ℂ) (lowering (realProfile F) x y) := by
  have hX : DifferentiableAt ℝ (fun t : ℝ => realProfile F t y) x := by
    change DifferentiableAt ℝ (F ∘ (fun t : ℝ => complexPoint t y)) x
    exact hF.comp x (by unfold complexPoint; fun_prop)
  have hY : DifferentiableAt ℝ (realProfile F x) y := by
    change DifferentiableAt ℝ (F ∘ (fun t : ℝ => complexPoint x t)) y
    exact hF.comp y (by unfold complexPoint; fun_prop)
  have hDX : partialX (realProfile (conjugate F)) x y =
      (starRingEnd ℂ) (partialX (realProfile F) x y) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hX.hasDerivAt).deriv
  have hDY : partialY (realProfile (conjugate F)) x y =
      (starRingEnd ℂ) (partialY (realProfile F) x y) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y hY.hasDerivAt).deriv
  rw [raising, hDX, hDY]
  simp only [lowering, map_sub, map_add, map_mul, map_neg, map_div₀, map_one, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal, neg_neg, realProfile, conjugate]

private def quarterHeight (z : ℍ) : ℂ := (z.im ^ (1 / 4 : ℝ) : ℝ)

private theorem quarterHeight_ne_zero (z : ℍ) : quarterHeight z ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos z.im_pos _).ne'

private theorem partner_mul_height (F : ℂ → ℂ) (z : ℍ) :
    partnerOnUpper (conjugate F) z * quarterHeight z = F z := by
  have h : z.im ^ (-(1 / 4 : ℝ)) * z.im ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add z.im_pos, neg_add_cancel, Real.rpow_zero]
  unfold partnerOnUpper holomorphicPartner conjugate quarterHeight
  rw [starRingEnd_self_apply]
  calc
    _ = (((z.im ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ)) * F z := by ring
    _ = _ := by rw [← Complex.ofReal_mul, h, Complex.ofReal_one, one_mul]

theorem gammaZero_positive_lowering_eq_const_mul_eta {N : ℕ} (hN : 0 < N) (hN24 : N < 24)
    {F : ℂ → ℂ}
    (hLaw : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ,
      F (g • z : ℍ) = positivePhase g z * F z)
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ F z)
    (hKernel : ∀ x y : ℝ, 0 < y → lowering (realProfile F) x y = 0)
    (hMass : (∫⁻ z in cosetCells (CongruenceSubgroup.Gamma0 N) ModularGroup.fd,
      normSquareDensity F z) < ⊤) :
    ∃ c : ℂ, ∀ z : ℍ, F z = c * etaMaass z := by
  let G := conjugate F
  let f := partnerOnUpper G
  have hGDiff (z : ℂ) (hz : 0 < z.im) : DifferentiableAt ℝ G z :=
    Complex.differentiable_conj.differentiableAt.comp z (hF z hz)
  have hGRaise (x y : ℝ) (hy : 0 < y) : raising (realProfile G) x y = 0 := by
    have hFxy := hF (complexPoint x y) (by simpa only [complexPoint_im] using hy)
    rw [G, raising_conjugate hFxy, hKernel x y hy, map_zero]
  have hHol : MDiff f := partnerOnUpper_holomorphic hGDiff hGRaise
  have hAgree (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
      f (g • z) * ModularForm.eta z = f z * ModularForm.eta (g • z : ℍ) := by
    have he : etaMaass (g • z) * F z = etaMaass z * F (g • z : ℍ) := by
      rw [etaMaass_transform, hLaw g hg z]
      ring
    change quarterHeight (g • z) * ModularForm.eta (g • z : ℍ) * F z =
      quarterHeight z * ModularForm.eta z * F (g • z : ℍ) at he
    rw [← partner_mul_height F z, ← partner_mul_height F (g • z)] at he
    change quarterHeight (g • z) * ModularForm.eta (g • z : ℍ) * (f z * quarterHeight z) =
      quarterHeight z * ModularForm.eta z * (f (g • z) * quarterHeight (g • z)) at he
    apply mul_left_cancel₀ (mul_ne_zero (quarterHeight_ne_zero (g • z)) (quarterHeight_ne_zero z))
    linear_combination -he
  have hCont : Continuous (fun z : ℍ => G z) := by
    refine continuous_iff_continuousAt.mpr (fun z => ?_)
    exact (hGDiff z z.im_pos).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt
  have hNorm (z : ℍ) : ‖G z‖ = ‖F z‖ := Complex.norm_conj _
  have hInv (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
      ‖G (g • z : ℍ)‖ = ‖G z‖ := by
    rw [hNorm, hNorm, hLaw g hg z, norm_mul, positivePhase_norm, one_mul]
  have hMassG : (∫⁻ z in cosetCells (CongruenceSubgroup.Gamma0 N) ModularGroup.fd,
      normSquareDensity G z) < ⊤ := by
    simpa only [normSquareDensity, hNorm] using hMass
  have hStrip (g : SL(2, ℤ)) : IntegrableOn
      (HolomorphicStripEnergy.weightedEnergy (Paper8EtaNormalizedCuspTranslate.cuspTranslate f g)
        (N : ℝ)) (Ioi 1) :=
    (maassStripEnergy_integrable_of_global_mass hCont.measurable hInv hMassG g N).congr_fun
      (fun y hy => (partner_weightedEnergy_eq_maassStripEnergy G g (N : ℝ) (zero_lt_one.trans hy)).symm)
      measurableSet_Ioi
  obtain ⟨c, hc⟩ :=
    Paper8EtaWeightedCuspRigidity.gammaZero_eq_const_mul_eta_of_weighted_LTwo hN hN24 hHol hAgree hStrip
  refine ⟨c, fun z => ?_⟩
  calc
    F z = f z * quarterHeight z := (partner_mul_height F z).symm
    _ = c * etaMaass z := by
      rw [hc]
      unfold etaMaass quarterHeight
      ring

end
end ManuscriptAudit.Paper8EtaPositiveCriticalRigidity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EtaPositiveCriticalRigidity.gammaZero_positive_lowering_eq_const_mul_eta
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
