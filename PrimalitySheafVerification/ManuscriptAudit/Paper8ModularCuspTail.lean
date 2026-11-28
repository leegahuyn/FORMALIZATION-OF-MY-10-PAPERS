import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.WithDensity
import PrimalitySheafVerification.ManuscriptAudit.Paper8ModularHeightCutoff

/-! Global finite Maass mass has vanishing mass in the invariant high cusp tails. -/

namespace ManuscriptAudit.Paper8ModularCuspTail

open Set Filter MeasureTheory UpperHalfPlane Paper8ModularHeightCutoff
open scoped MatrixGroups ENNReal Topology

set_option maxHeartbeats 1200000 in
theorem isOpen_height_above (Y : ℝ) : IsOpen {z : ℍ | Y < maximumHeight z} := by
  have hSet : {z : ℍ | Y < maximumHeight z} =
      ⋃ g : SL(2, ℤ), {z : ℍ | Y < (g • z).im} := by
    ext z
    constructor
    · intro hz
      let g := Classical.choose (ModularGroup.exists_max_im z)
      change Y < (g • z).im at hz
      exact mem_iUnion.mpr ⟨g, hz⟩
    · intro hz
      obtain ⟨g, hg⟩ := mem_iUnion.mp hz
      exact hg.trans_le (im_smul_le_maximumHeight z g)
  rw [hSet]
  apply isOpen_iUnion
  intro g
  have hAction : Continuous (fun z : ℍ => g • z) := by
    simpa only [ModularGroup.sl_moeb] using (continuous_const_smul (g : GL (Fin 2) ℝ))
  exact isOpen_lt continuous_const (UpperHalfPlane.continuous_im.comp hAction)

theorem lintegral_cusp_tail_tendsto_zero {S : Set ℍ} (hS : MeasurableSet S) {D : ℍ → ℝ≥0∞}
    (hMass : (∫⁻ z in S, D z) < ⊤) :
    Tendsto (fun N : ℕ => ∫⁻ z in S ∩ {z : ℍ | (N : ℝ) < maximumHeight z}, D z)
      atTop (𝓝 0) := by
  let ν : Measure ℍ := ((volume : Measure ℍ).restrict S).withDensity D
  let T (N : ℕ) : Set ℍ := {z : ℍ | (N : ℝ) < maximumHeight z}
  have hT (N : ℕ) : MeasurableSet (T N) := (isOpen_height_above (N : ℝ)).measurableSet
  have hAll : ν univ < ⊤ := by
    simpa only [ν, withDensity_apply D MeasurableSet.univ, Measure.restrict_univ] using hMass
  have hAnti : Antitone T := by
    intro M N hMN z hz
    exact lt_of_le_of_lt (by exact_mod_cast hMN) hz
  have hEmpty : (⋂ N : ℕ, T N) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨N, hN⟩ := exists_nat_gt (maximumHeight z)
    exact (not_lt_of_ge hN.le) (mem_iInter.mp hz N)
  have hFin : ∃ N : ℕ, ν (T N) ≠ ⊤ :=
    ⟨0, ((measure_mono (subset_univ (T 0))).trans_lt hAll).ne⟩
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun N => (hT N).nullMeasurableSet) hAnti hFin
  rw [hEmpty, measure_empty] at h
  refine h.congr (fun N => ?_)
  change ν (T N) = ∫⁻ z in S ∩ T N, D z
  rw [ν, withDensity_apply D (hT N), Measure.restrict_restrict' hS, inter_comm (T N) S]

end ManuscriptAudit.Paper8ModularCuspTail

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8ModularCuspTail.lintegral_cusp_tail_tendsto_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
