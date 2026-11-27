import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaNormalizedCuspTranslate

/-!
# Integral-weight product associated to the inverse squared eta multiplier

The square of a holomorphic half-weight section with inverse squared eta
multiplier times the square of eta has the native weight-two slash law.
Its cusp translates are periodic and their norms recover the eta ratio.
-/

namespace ManuscriptAudit.Paper8EtaInverseMultiplier

open Function UpperHalfPlane ModularForm
open Paper8ActualEtaSquaredModularity Paper8ActualEtaNormCusp Paper8EtaNormalizedCuspTranslate
open scoped MatrixGroups Manifold ModularForm

noncomputable section

def InverseSquaredAutomorphy (H : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) : Prop :=
  ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ,
    f (g • z) ^ 2 = (squaredMultiplier g)⁻¹ * (denominator g z * f z ^ 2)

def weightTwoProduct (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  f z ^ 2 * ModularForm.eta z ^ 2

theorem weightTwoProduct_holomorphic {f : ℍ → ℂ} (hF : MDiff f) :
    MDiff (weightTwoProduct f) := by
  exact (hF.pow 2).mul (Paper8EtaRigidity.eta_holomorphic.pow 2)

theorem weightTwoProduct_slash_eq {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hF : InverseSquaredAutomorphy H f) (g : SL(2, ℤ)) (hg : g ∈ H) :
    weightTwoProduct f ∣[(2 : ℤ)] g = weightTwoProduct f := by
  funext z
  apply (ModularForm.slash_action_eq'_iff 2 (weightTwoProduct f) g z).2
  change weightTwoProduct f (g • z) = denominator g z ^ (2 : ℤ) * weightTwoProduct f z
  rw [zpow_ofNat]
  unfold weightTwoProduct
  rw [hF g hg z, eta_squared_transform]
  field_simp [squaredMultiplier_ne_zero g] <;> ring

def weightTwoTranslate (f : ℍ → ℂ) (g : SL(2, ℤ)) : ℍ → ℂ :=
  weightTwoProduct f ∣[(2 : ℤ)] g

theorem weightTwoTranslate_holomorphic {f : ℍ → ℂ} (hF : MDiff f) (g : SL(2, ℤ)) :
    MDiff (weightTwoTranslate f g) :=
  (weightTwoProduct_holomorphic hF).slash (2 : ℤ) (g : GL (Fin 2) ℝ)

theorem weightTwoTranslate_periodic {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hF : InverseSquaredAutomorphy H f) (g : SL(2, ℤ)) {w : ℕ}
    (hMem : g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H) :
    Periodic (weightTwoTranslate f g ∘ ofComplex) (w : ℝ) := by
  have hSlash : weightTwoTranslate f g ∣[(2 : ℤ)] (ModularGroup.T ^ (w : ℤ)) =
      weightTwoTranslate f g := by
    unfold weightTwoTranslate
    calc
      _ = weightTwoProduct f ∣[(2 : ℤ)] (g * ModularGroup.T ^ (w : ℤ)) :=
        (SlashAction.slash_mul 2 g (ModularGroup.T ^ (w : ℤ)) (weightTwoProduct f)).symm
      _ = weightTwoProduct f ∣[(2 : ℤ)] ((g * ModularGroup.T ^ (w : ℤ) * g⁻¹) * g) := by
        simp [mul_assoc]
      _ = _ := by rw [SlashAction.slash_mul, weightTwoProduct_slash_eq hF _ hMem]
  have hShift (z : ℍ) : weightTwoTranslate f g (ModularGroup.T ^ (w : ℤ) • z) =
      weightTwoTranslate f g z := by
    have hD : denominator (ModularGroup.T ^ (w : ℤ)) z = 1 := by
      simp [denominator, ModularGroup.coe_T_zpow]
    have h := congrFun hSlash z
    rw [SL_slash_apply, ← denominator_eq, hD, one_zpow, mul_one] at h
    exact h
  intro z
  by_cases! hz : 0 < z.im
  · have hz' : 0 < (z + ((w : ℝ) : ℂ)).im := by simpa using hz
    have hT : ModularGroup.T ^ (w : ℤ) • (⟨z, hz⟩ : ℍ) = ⟨z + ((w : ℝ) : ℂ), hz'⟩ := by
      rw [UpperHalfPlane.modular_T_zpow_smul]
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hz',
      ofComplex_apply_of_im_pos hz, hT] using hShift (⟨z, hz⟩ : ℍ)
  · have hz' : (z + ((w : ℝ) : ℂ)).im ≤ 0 := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_eq_of_im_nonpos hz' hz]

theorem norm_weightTwoTranslate (f : ℍ → ℂ) (g : SL(2, ℤ)) (z : ℍ) :
    ‖weightTwoTranslate f g z‖ = ‖etaRatio f (g • z)‖ ^ 2 * ‖ModularForm.eta z‖ ^ 4 := by
  have hD : ‖denominator g z‖ ≠ 0 := norm_ne_zero_iff.mpr (denominator_ne_zero g z)
  have hEta : ‖ModularForm.eta z‖ ≠ 0 := norm_ne_zero_iff.mpr (ModularForm.eta_ne_zero z.im_pos)
  rw [weightTwoTranslate, SL_slash_apply, ← denominator_eq]
  simp only [weightTwoProduct, etaRatio, norm_mul, norm_pow, norm_div, norm_zpow,
    zpow_neg, zpow_ofNat, div_pow]
  rw [eta_norm_square_transform]
  field_simp [hD, hEta] <;> ring

theorem etaRatio_pow_twentyFour_invariant {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hF : InverseSquaredAutomorphy H f) (g : SL(2, ℤ)) (hg : g ∈ H) (z : ℍ) :
    etaRatio f (g • z) ^ 24 = etaRatio f z ^ 24 := by
  have hRatio : etaRatio f (g • z) ^ 2 =
      ((squaredMultiplier g)⁻¹) ^ 2 * etaRatio f z ^ 2 := by
    simp only [etaRatio, div_pow]
    rw [hF g hg z, eta_squared_transform]
    field_simp [squaredMultiplier_ne_zero g, denominator_ne_zero g z,
      ModularForm.eta_ne_zero z.im_pos] <;> ring
  calc
    _ = (etaRatio f (g • z) ^ 2) ^ 12 := by rw [← pow_mul]
    _ = (etaRatio f z ^ 2) ^ 12 := by
      rw [hRatio, mul_pow, ← pow_mul, ← inv_pow]
      change (squaredMultiplier g ^ 24)⁻¹ * (etaRatio f z ^ 2) ^ 12 = _
      have h : squaredMultiplier g ^ 24 = 1 := by
        calc
          _ = (squaredMultiplier g ^ 12) ^ 2 := by rw [← pow_mul]
          _ = _ := by simp [squaredMultiplier_pow_twelve]
      simp [h]
    _ = _ := by rw [← pow_mul]

end
end ManuscriptAudit.Paper8EtaInverseMultiplier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaInverseMultiplier.weightTwoProduct_holomorphic,
      ``ManuscriptAudit.Paper8EtaInverseMultiplier.weightTwoProduct_slash_eq,
      ``ManuscriptAudit.Paper8EtaInverseMultiplier.weightTwoTranslate_holomorphic,
      ``ManuscriptAudit.Paper8EtaInverseMultiplier.weightTwoTranslate_periodic,
      ``ManuscriptAudit.Paper8EtaInverseMultiplier.norm_weightTwoTranslate,
      ``ManuscriptAudit.Paper8EtaInverseMultiplier.etaRatio_pow_twentyFour_invariant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
