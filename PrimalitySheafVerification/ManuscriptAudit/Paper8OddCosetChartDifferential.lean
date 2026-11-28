import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCosetChartEnergy

/-! Continuity of the actual odd cusp-chart derivatives on the upper half-plane. -/

namespace ManuscriptAudit.Paper8OddCosetChartDifferential

open Filter Set UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8EtaHalfWeightPhase Paper8NegativeEtaPhaseDifferential
open Paper8MaassCovariantGeometry Paper8MaassCovariantPullback
open Paper8OddCosetChartTransition Paper8OddCosetChartEnergy
open Paper8OddMaassHilbertCore Paper8OddMaassCovariantGradient
open Paper8EtaCosetMass FiniteIndexWeightZeroCosets
open scoped ContDiff MatrixGroups Topology

noncomputable section

theorem oddCore_fderiv_apply_continuous (f : OddSmoothCompactCore) :
    Continuous (fun p : ℍ × ℂ => fderiv ℝ (f : ℂ → ℂ) (p.1 : ℂ) p.2) := by
  let S : Set ℂ := {w | 0 < w.im}
  let L : ℍ × ℂ → ℂ × ℂ := fun p => ((p.1 : ℂ), p.2)
  have hS : IsOpen S := isOpen_lt continuous_const Complex.continuous_im
  have hC : ContDiffOn ℝ 1 (f : ℂ → ℂ) S := f.2.2.1.of_le (by norm_num)
  have hL : Continuous L := (UpperHalfPlane.continuous_coe.comp continuous_fst).prodMk continuous_snd
  have hMap : ∀ p, L p ∈ S ×ˢ (univ : Set ℂ) := fun p => ⟨p.1.im_pos, mem_univ _⟩
  have hCont := (hC.continuousOn_fderivWithin_apply hS.uniqueDiffOn (le_refl 1)).comp_continuous hL hMap
  refine hCont.congr fun p => ?_
  change fderivWithin ℝ (f : ℂ → ℂ) S (p.1 : ℂ) p.2 = fderiv ℝ (f : ℂ → ℂ) (p.1 : ℂ) p.2
  rw [fderivWithin_of_isOpen hS p.1.im_pos]

theorem negativePhase_continuous (g : SL(2, ℤ)) : Continuous (negativePhase g) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (negativeEtaPhaseComplex_differentiableAt g z).continuousAt.comp
    UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_apply, negativeEtaPhaseComplex_coe] using h

private theorem phase_inv_continuous (g : SL(2, ℤ)) : Continuous (fun z : ℍ => (negativePhase g z)⁻¹) := by
  apply (negativePhase_continuous g).inv₀
  intro z hz
  have h := negativePhase_norm g z
  simp [hz] at h

theorem oddCosetPullback_continuous (f : OddSmoothCompactCore) (q : levelFourRightCoset) :
    Continuous (fun z : ℍ => oddCosetPullback f q z) := by
  let g := cellRepresentative (CongruenceSubgroup.Gamma0 4) q
  have hMove : Continuous (fun z : ℍ => g • z) := by
    simpa only [ModularGroup.sl_moeb] using (continuous_const_smul (g : GL (Fin 2) ℝ))
  have h := (phase_inv_continuous g).mul ((oddCore_continuous f).comp hMove)
  simpa only [oddCosetPullback, oddMaassPullback_coe, g] using h

theorem oddCosetPullback_directional_continuous (f : OddSmoothCompactCore)
    (q : levelFourRightCoset) (v : ℂ) :
    Continuous (fun z : ℍ => fderiv ℝ (oddCosetPullback f q) (z : ℂ) v) := by
  let g := cellRepresentative (CongruenceSubgroup.Gamma0 4) q
  have hMove : Continuous (fun z : ℍ => g • z) := by
    simpa only [ModularGroup.sl_moeb] using (continuous_const_smul (g : GL (Fin 2) ℝ))
  have hDen : Continuous (fun z : ℍ => denominator g z) := by
    unfold denominator
    fun_prop
  have hDenNe (z : ℍ) : denominator g z ≠ 0 := denominator_ne_zero g z
  have hV : Continuous (fun z : ℍ => ((denominator g z) ^ 2)⁻¹ * v) :=
    ((hDen.pow 2).inv₀ (fun z => pow_ne_zero 2 (hDenNe z))).mul continuous_const
  have hDer := (oddCore_fderiv_apply_continuous f).comp (hMove.prodMk hV)
  have hRatio : Continuous (fun z : ℍ => (g 1 0 : ℂ) * v / denominator g z) :=
    continuous_const.div hDen hDenNe
  have hCorrection : Continuous (fun z : ℍ => (Complex.I / 2) *
      (((g 1 0 : ℂ) * v / denominator g z).im : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hRatio))
  have h := (phase_inv_continuous g).mul
    (hDer.add (hCorrection.mul ((oddCore_continuous f).comp hMove)))
  refine h.congr fun z => ?_
  change (negativePhase g z)⁻¹ *
      (fderiv ℝ (f : ℂ → ℂ) ((g • z : ℍ) : ℂ) (((denominator g z) ^ 2)⁻¹ * v) +
      (Complex.I / 2) * (((g 1 0 : ℂ) * v / denominator g z).im : ℂ) * (f : ℂ → ℂ) (g • z : ℍ)) =
        fderiv ℝ (oddCosetPullback f q) (z : ℂ) v
  exact (oddMaassPullback_fderiv g z (oddCore_differentiableAt f (g • z)) v).symm

theorem oddCosetPullback_energy_continuous (f : OddSmoothCompactCore) (q : levelFourRightCoset) :
    Continuous (maassCovariantEnergy (oddCosetPullback f q)) := by
  have hV (v : ℂ) : Continuous (fun z : ℍ => maassCovariantValue (oddCosetPullback f q) z v) := by
    unfold maassCovariantValue
    exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
      (oddCosetPullback_directional_continuous f q v)).add
      (continuous_const.mul (oddCosetPullback_continuous f q))
  unfold maassCovariantEnergy
  exact ((hV 1).norm.pow 2).add ((hV Complex.I).norm.pow 2)

end
end ManuscriptAudit.Paper8OddCosetChartDifferential

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCosetChartDifferential.oddCosetPullback_energy_continuous
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
