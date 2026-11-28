import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.Congr
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCurlCalculus
import PrimalitySheafVerification.ManuscriptAudit.Paper8WeightTwoCosetTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCosetMass

/-! Hyperbolic curl of the native weight-two coset trace. -/

namespace ManuscriptAudit.Paper8MaassTraceCurl

open Filter Function Set UpperHalfPlane ModularForm
open Paper8ActualEtaSquaredModularity Paper8MaassWirtinger Paper8MaassCurlCalculus
open Paper8WeightTwoCosetTrace FiniteIndexWeightZeroCosets
open Paper8EtaCosetMass (cellRepresentative cellRepresentative_mk)
open scoped MatrixGroups ModularForm Topology

noncomputable section

def weightedCurl (J : ℂ → ℂ) (z : ℍ) : ℂ := ((z.im ^ 2 : ℝ) : ℂ) * complexCurl J z

def slashComplex (J : ℂ → ℂ) (g : SL(2, ℤ)) (w : ℂ) : ℂ :=
  J (fractionalLinear g w) * (denominator g w ^ 2)⁻¹

theorem slashComplex_coe (J : ℂ → ℂ) (g : SL(2, ℤ)) (z : ℍ) :
    slashComplex J g z = ((fun u : ℍ => J u) ∣[(2 : ℤ)] g) z := by
  rw [slashComplex, fractionalLinear_eq, SL_slash_apply, ← denominator_eq, zpow_neg, zpow_ofNat]

theorem slashComplex_differentiableAt (J : ℂ → ℂ) (g : SL(2, ℤ)) (z : ℍ)
    (hJ : DifferentiableAt ℝ J (g • z : ℍ)) :
    DifferentiableAt ℝ (slashComplex J g) z := by
  have hC : DifferentiableAt ℝ (J ∘ fractionalLinear g) z := by
    have h : DifferentiableAt ℝ J (fractionalLinear g z) := by rw [fractionalLinear_eq]; exact hJ
    exact h.comp _ ((fractionalLinear_hasDerivAt g z).differentiableAt.restrictScalars ℝ)
  have hD : DifferentiableAt ℂ (denominator g) z := by unfold denominator; fun_prop
  have hI := (hD.pow 2).inv (pow_ne_zero 2 (denominator_ne_zero g z))
  exact hC.mul (hI.restrictScalars ℝ)

private theorem weightedCurl_factor (g : SL(2, ℤ)) (z : ℍ) :
    ((z.im ^ 2 : ℝ) : ℂ) * (denominator g z ^ 2)⁻¹ *
        (starRingEnd ℂ) ((denominator g z ^ 2)⁻¹) =
      (((g • z : ℍ).im ^ 2 : ℝ) : ℂ) := by
  let d := denominator g z
  have hIm : (g • z : ℍ).im = z.im / ‖d‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, ← denominator_eq, Complex.normSq_eq_norm_sq]
  rw [hIm]
  change ((z.im ^ 2 : ℝ) : ℂ) * (d ^ 2)⁻¹ * (starRingEnd ℂ) ((d ^ 2)⁻¹) = _
  have hD : d ^ 2 * ((starRingEnd ℂ) d) ^ 2 = (((‖d‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
    rw [← mul_pow, Complex.mul_conj', Complex.ofReal_pow]
  have hInv : (starRingEnd ℂ) ((d ^ 2)⁻¹) = (((starRingEnd ℂ) d) ^ 2)⁻¹ := by
    rw [map_inv₀, map_pow]
  rw [hInv, mul_assoc, show (d ^ 2)⁻¹ * (((starRingEnd ℂ) d) ^ 2)⁻¹ =
    (d ^ 2 * ((starRingEnd ℂ) d) ^ 2)⁻¹ by simp [mul_inv_rev, mul_comm], hD]
  push_cast
  rw [div_pow, div_eq_mul_inv]

theorem weightedCurl_slashComplex (J : ℂ → ℂ) (g : SL(2, ℤ)) (z : ℍ)
    (hJ : DifferentiableAt ℝ J (g • z : ℍ)) :
    weightedCurl (slashComplex J g) z = weightedCurl J (g • z) := by
  have hJ' : DifferentiableAt ℝ J (fractionalLinear g z) := by rw [fractionalLinear_eq]; exact hJ
  have hD : DifferentiableAt ℂ (denominator g) z := by unfold denominator; fun_prop
  have hI := (hD.pow 2).inv (pow_ne_zero 2 (denominator_ne_zero g z))
  have hInv : DifferentiableAt ℂ (fun w : ℂ => (denominator g w ^ 2)⁻¹) z := hI
  unfold weightedCurl slashComplex
  rw [complexCurl_pullback_holomorphic hJ' (fractionalLinear_hasDerivAt g z).differentiableAt hInv,
    (fractionalLinear_hasDerivAt g z).deriv, fractionalLinear_eq]
  rw [← mul_assoc, ← mul_assoc, weightedCurl_factor]

theorem weightedCurl_trace (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (J : ℂ → ℂ)
    (hJ : ∀ z : ℍ, DifferentiableAt ℝ J z)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H →
      (fun z : ℍ => J z) ∣[(2 : ℤ)] h = fun z : ℍ => J z) (z : ℍ) :
    letI := rightCosetFintype H
    weightedCurl (fun w : ℂ => trace H (fun u : ℍ => J u) hInv (ofComplex w)) z =
      ∑ q : RightCoset H, weightedCurl J (cellRepresentative H q • z) := by
  letI := rightCosetFintype H
  let A (q : RightCoset H) := slashComplex J (cellRepresentative H q)
  have hEq :
      (fun w : ℂ => trace H (fun u : ℍ => J u) hInv (ofComplex w)) =ᶠ[𝓝 (z : ℂ)]
        (fun w : ℂ => ∑ q : RightCoset H, A q w) := by
    filter_upwards [Complex.continuous_im.continuousAt.tendsto.eventually (Ioi_mem_nhds z.im_pos)]
      with w hw
    let u : ℍ := ⟨w, hw⟩
    change trace H (fun u : ℍ => J u) hInv (ofComplex w) =
      ∑ q : RightCoset H, A q w
    rw [ofComplex_apply_of_im_pos hw]
    unfold trace
    apply Finset.sum_congr rfl
    intro q _
    change cosetSlash H (fun u : ℍ => J u) hInv q u = slashComplex J (cellRepresentative H q) u
    conv_lhs => rw [← cellRepresentative_mk H q, cosetSlash_mk]
    rw [slashComplex_coe]
  have hAD (q : RightCoset H) : DifferentiableAt ℝ (A q) z :=
    slashComplex_differentiableAt J (cellRepresentative H q) z (hJ _)
  classical
  change weightedCurl (fun w : ℂ => trace H (fun u : ℍ => J u) hInv (ofComplex w)) z =
    ∑ q : RightCoset H, weightedCurl J (cellRepresentative H q • z)
  unfold weightedCurl complexCurl
  rw [hEq.fderiv_eq (𝕜 := ℝ), fderiv_fun_sum (fun q _ => hAD q)]
  simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  exact weightedCurl_slashComplex J (cellRepresentative H q) z (hJ _)

end
end ManuscriptAudit.Paper8MaassTraceCurl

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassTraceCurl.weightedCurl_trace
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
