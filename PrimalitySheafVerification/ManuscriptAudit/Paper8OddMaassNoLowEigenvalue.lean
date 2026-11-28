import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassGapEnergy
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassCriticalEigenvalue

/-! No nonzero odd level-four Maass eigenfunction at or below the actual eta eigenvalue. -/

namespace ManuscriptAudit.Paper8OddMaassNoLowEigenvalue

open Filter Set MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8EtaCriticalOddVanishing Paper8MaassCriticalHolomorphic Paper8OddMaassSmoothFactorization
open Paper8MaassGapEnergy Paper8OddGlobalCutoffGreen Paper8OddGlobalCutoffEnergy
open Paper8OddGlobalCriticalVanishing Paper8OddMaassCriticalEigenvalue
open Paper8ModularHeightCutoff Paper8ModularCuspTail Paper8MaassStripFubini Paper8EtaCosetBoundary
open Paper8EtaCosetMass (cosetCells)
open scoped MatrixGroups ENNReal Topology

noncomputable section

local notation "Γ₄" => CongruenceSubgroup.Gamma0 4

private theorem real_cusp_mass_tendsto_zero {F : ℂ → ℂ}
    (hF : Continuous (fun z : ℍ => F z))
    (hMass : (∫⁻ z in levelFourCells, normSquareDensity F z) < ⊤) :
    Tendsto (fun n : ℕ => ∫ z in levelFourCells ∩ {u : ℍ | (n : ℝ) < maximumHeight u}, ‖F z‖ ^ 2)
      atTop (𝓝 0) := by
  let T (n : ℕ) : Set ℍ := levelFourCells ∩ {u : ℍ | (n : ℝ) < maximumHeight u}
  have hTail := lintegral_cusp_tail_tendsto_zero measurable_levelFourCells hMass
  have hTo := (ENNReal.continuousAt_toReal (x := 0) (by simp)).tendsto.comp hTail
  have hEq (n : ℕ) : (∫ z in T n, ‖F z‖ ^ 2) =
      (∫⁻ z in T n, normSquareDensity F z).toReal := by
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun z : ℍ => sq_nonneg ‖F z‖))
      ((hF.norm.pow 2).aestronglyMeasurable)
  have hFun : (fun n : ℕ => ∫ z in T n, ‖F z‖ ^ 2) =
      (fun n : ℕ => (∫⁻ z in T n, normSquareDensity F z).toReal) := funext hEq
  change Tendsto (fun n : ℕ => ∫ z in T n, ‖F z‖ ^ 2) atTop (𝓝 0)
  rw [hFun]
  simpa only [Function.comp_def, ENNReal.toReal_zero, T] using hTo

theorem odd_maass_below_critical_eigenfunction_eq_zero {F : ℂ → ℂ} {λ : ℝ}
    (hLaw : OddMaassLaw F) (hλ : λ < 3 / 16)
    (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    (hEigen : ∀ x y : ℝ, 0 < y →
      maassDelta (-1 / 2) (realProfile F) x y = (λ : ℂ) * realProfile F x y)
    (hMass : (∫⁻ z in levelFourCells, normSquareDensity F z) < ⊤) :
    ∀ z : ℍ, F z = 0 := by
  let G := raisedField F
  let δ := λ - 3 / 16
  have hF1 : ContDiffOn ℝ 1 F {w : ℂ | 0 < w.im} := hF.of_le (by norm_num)
  have hG : ContDiffOn ℝ 1 G {w : ℂ | 0 < w.im} := raisedField_contDiffOn hF
  have hOpenU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdF (v : ℂ) (hv : 0 < v.im) : DifferentiableAt ℝ F v :=
    ((hF v hv).contDiffAt (hOpenU.mem_nhds hv)).differentiableAt (by norm_num)
  have hCont : Continuous (fun z : ℍ => F z) :=
    hF.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  have hJ (Y : ℝ) (hY : 2 < Y) : ContDiffOn ℝ 1 (Paper8MaassCutoffFlux.cutoffFlux Y F G)
      {w : ℂ | 0 < w.im} := cutoffFlux_contDiffOn_of_realSmooth hY hF1 hG
  obtain ⟨C, _, hBound⟩ := odd_shifted_cutoff_energy_le_tail (δ := δ) hLaw hF1 hG hJ
    (raisedField_realProfile hF) (raisedField_adjoint_of_eigenvalue hF hEigen) hMass
  let T (n : ℕ) : Set ℍ := levelFourCells ∩ {u : ℍ | (n : ℝ) < maximumHeight u}
  let M (n : ℕ) := ∫ z in T n, ‖F z‖ ^ 2
  have hδ : 0 < -2 * δ := by unfold δ; linarith
  have hTendsto : Tendsto (fun n : ℕ => (C ^ 2 / (-2 * δ)) * M n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := C ^ 2 / (-2 * δ))).mul (real_cusp_mass_tendsto_zero hCont hMass)
  have hCutoff : Tendsto (fun n : ℕ =>
      ∫ z in levelFourCells, cutoffEnergy ((n : ℝ) + 3) F z) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hTendsto
    · intro n
      exact integral_nonneg (fun z => sq_nonneg _)
    · intro n
      let Y : ℝ := (n : ℝ) + 3
      have hY : 2 < Y := by
        have hNat : 0 ≤ (n : ℝ) := by positivity
        dsimp only [Y]
        linarith
      have hB := hBound Y hY (n : ℝ) (by dsimp only [Y]; linarith)
      have hA : 0 ≤ ∫ z in levelFourCells, cutoffEnergy Y G z :=
        integral_nonneg (fun z => sq_nonneg _)
      have hB' : (∫ z in levelFourCells, cutoffEnergy Y F z) * (-2 * δ) ≤ C ^ 2 * M n := by
        change (∫ z in levelFourCells, cutoffEnergy Y G z) -
          2 * δ * (∫ z in levelFourCells, cutoffEnergy Y F z) ≤ C ^ 2 * M n at hB
        linarith
      calc
        _ ≤ (C ^ 2 * M n) / (-2 * δ) := (le_div_iff₀ hδ).2 hB'
        _ = _ := by ring
  letI := actualVolume_isOpenPosMeasure
  let O := cosetCells Γ₄ ModularGroup.fdo
  have hO : IsOpen O := levelFourOpenCells_isOpen
  have hAE := raisingField_ae_zero_on_cells hdF hCutoff
  have hRestrict : (volume : Measure ℍ).restrict levelFourCells = volume.restrict O :=
    Measure.restrict_congr_set (closed_cells_ae_eq_open Γ₄)
  rw [hRestrict] at hAE
  have hOpen : EqOn (fun z : ℍ => F z) (fun _ => 0) O :=
    Measure.eqOn_open_of_ae_eq hAE hO hCont.continuousOn continuousOn_const
  have hAll : (fun z : ℍ => F z) =ᵐ[(volume : Measure ℍ)] (fun _ => 0) := by
    filter_upwards [open_cells_meet_ae_orbit Γ₄] with z hz
    obtain ⟨g, u, hu, rfl⟩ := hz
    have hZ : F u = 0 := hOpen hu
    rw [hLaw g u, hZ, mul_zero]
  intro z
  exact congrFun (Measure.eq_of_ae_eq hAll hCont continuous_const) z

theorem odd_maass_at_or_below_eta_eigenfunction_eq_zero {F : ℂ → ℂ} {λ : ℝ}
    (hLaw : OddMaassLaw F) (hλ : λ ≤ 3 / 16)
    (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    (hEigen : ∀ x y : ℝ, 0 < y →
      maassDelta (-1 / 2) (realProfile F) x y = (λ : ℂ) * realProfile F x y)
    (hMass : (∫⁻ z in levelFourCells, normSquareDensity F z) < ⊤) :
    ∀ z : ℍ, F z = 0 := by
  rcases lt_or_eq_of_le hλ with h | rfl
  · exact odd_maass_below_critical_eigenfunction_eq_zero hLaw h hF hEigen hMass
  · apply odd_maass_critical_eigenfunction_eq_zero hLaw hF ?_ hMass
    intro x y hy
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hEigen x y hy

end
end ManuscriptAudit.Paper8OddMaassNoLowEigenvalue

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassNoLowEigenvalue.odd_maass_at_or_below_eta_eigenfunction_eq_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
