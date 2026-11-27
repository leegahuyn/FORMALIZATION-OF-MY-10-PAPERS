import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FiniteIndexWeightZero
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCuspWidths
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaRatioCuspLimit

/-! Holomorphic rigidity for matching eta automorphy on narrow-cusp congruence groups. -/

namespace ManuscriptAudit.Paper8EtaRigidity

open Set Filter Function UpperHalfPlane ModularForm
open Paper8ActualEtaSquaredModularity
open scoped MatrixGroups Manifold ModularForm Topology

private theorem eta_holomorphic : MDiff (fun z : ℍ => ModularForm.eta z) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr
    (fun z hz => (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt) ?_
  intro z hz
  simp [Function.comp_def, ofComplex_apply_of_im_pos hz]

private theorem translate_holomorphic {F : ℍ → ℂ} (hF : MDiff F)
    (g : SL(2, ℤ)) : MDiff (fun z : ℍ => F (g • z)) := by
  have hSlash := hF.slash (0 : ℤ) (g : GL (Fin 2) ℝ)
  change MDiff (F ∣[(0 : ℤ)] g) at hSlash
  simpa only [SL_slash_def, UpperHalfPlane.sl_moeb, neg_zero, zpow_zero, mul_one] using hSlash

theorem translate_periodic_of_conjugatedTranslation_mem {H : Subgroup SL(2, ℤ)}
    {F : ℍ → ℂ} (hF : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ, F (g • z) = F z)
    (g : SL(2, ℤ)) {w : ℕ} (hMem : g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H) :
    Periodic ((fun z : ℍ => F (g • z)) ∘ ofComplex) (w : ℝ) := by
  have hShift (z : ℍ) : F (g • (ModularGroup.T ^ (w : ℤ) • z)) = F (g • z) := by
    calc
      _ = F (((g * ModularGroup.T ^ (w : ℤ) * g⁻¹) * g) • z) := by
        rw [← mul_smul]
        simp [mul_assoc]
      _ = _ := by
        rw [mul_smul]
        exact hF _ hMem _
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

private theorem bounded_of_tendsto {F : ℍ → ℂ} {L : ℂ} (h : Tendsto F atImInfty (𝓝 L)) :
    IsBoundedAtImInfty F := by
  have hZero : ZeroAtFilter atImInfty (F - Function.const ℍ L) := by
    simpa only [ZeroAtFilter, Pi.sub_def, Function.const_apply, sub_self] using
      h.sub (tendsto_const_nhds : Tendsto (fun _ : ℍ => L) atImInfty (𝓝 L))
  have hB := hZero.boundedAtFilter.add (const_boundedAtFilter atImInfty L)
  simpa only [IsBoundedAtImInfty, sub_add_cancel] using hB

theorem eq_const_mul_eta_of_matching_automorphy (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    {f : ℍ → ℂ} (hHol : MDiff f)
    (hAgree : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ,
      f (g • z) * ModularForm.eta z = f z * ModularForm.eta (g • z : ℍ))
    (hWidth : ∀ g : SL(2, ℤ), ∃ w : ℕ,
      0 < w ∧ w < 24 ∧ g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H)
    (hBound : ∀ g : SL(2, ℤ), ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ z : ℍ in atImInfty, ‖f (g • z)‖ ≤ M * Real.sqrt ‖denominator g z‖) :
    ∃ c : ℂ, ∀ z : ℍ, f z = c * ModularForm.eta z := by
  let F (z : ℍ) := f z / ModularForm.eta z
  have hInv (g : SL(2, ℤ)) (hg : g ∈ H) (z : ℍ) : F (g • z) = F z :=
    (div_eq_div_iff (ModularForm.eta_ne_zero (g • z : ℍ).im_pos)
      (ModularForm.eta_ne_zero z.im_pos)).2 (hAgree g hg z)
  have hFHol : MDiff F := by
    simpa only [F, Pi.div_def] using hHol.div eta_holomorphic (fun z : ℍ =>
      ModularForm.eta_ne_zero z.im_pos)
  have hFB (g : SL(2, ℤ)) : IsBoundedAtImInfty (fun z : ℍ => F (g • z)) := by
    obtain ⟨w, hw, hw24, hMem⟩ := hWidth g
    obtain ⟨M, hM, hB⟩ := hBound g
    obtain ⟨L, hL⟩ := Paper8EtaRatioCuspLimit.eta_ratio_limit g hw hw24 hM
      (translate_periodic_of_conjugatedTranslation_mem hInv g hMem) (translate_holomorphic hFHol g) hB
    exact bounded_of_tendsto hL
  obtain ⟨c, hc⟩ := FiniteIndexWeightZero.weight_zero_eq_const H F hInv hFHol hFB
  exact ⟨c, fun z => (div_eq_iff (ModularForm.eta_ne_zero z.im_pos)).1 (congrFun hc z)⟩

theorem gammaZero_eq_const_mul_eta {N : ℕ} (hN : 0 < N) (hN24 : N < 24)
    {f : ℍ → ℂ} (hHol : MDiff f)
    (hAgree : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ,
      f (g • z) * ModularForm.eta z = f z * ModularForm.eta (g • z : ℍ))
    (hBound : ∀ g : SL(2, ℤ), ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ z : ℍ in atImInfty, ‖f (g • z)‖ ≤ M * Real.sqrt ‖denominator g z‖) :
    ∃ c : ℂ, ∀ z : ℍ, f z = c * ModularForm.eta z := by
  letI : NeZero N := ⟨hN.ne'⟩
  exact eq_const_mul_eta_of_matching_automorphy (CongruenceSubgroup.Gamma0 N) hHol hAgree
    (fun g => ⟨N, hN, hN24, Paper8EtaCuspWidths.conjugatedTranslation_level N g⟩) hBound

end ManuscriptAudit.Paper8EtaRigidity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaRigidity.translate_periodic_of_conjugatedTranslation_mem,
      ``ManuscriptAudit.Paper8EtaRigidity.eq_const_mul_eta_of_matching_automorphy,
      ``ManuscriptAudit.Paper8EtaRigidity.gammaZero_eq_const_mul_eta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
