import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCovariantPullback
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCosetChartTransition
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassCovariantGradient

/-! The sum of covariant energies of the actual finite chart family is modular invariant. -/

namespace ManuscriptAudit.Paper8OddCosetChartEnergy

open Filter UpperHalfPlane
open Paper8MaassCovariantGeometry Paper8MaassCovariantPullback Paper8OddCosetChartTransition
open Paper8EtaCosetMass FiniteIndexWeightZeroCosets Paper8OddCrossCuspRows Paper8EtaHalfWeightPhase
open Paper8OddMaassHilbertCore Paper8OddMaassCovariantGradient
open Paper8EtaInverseWeightedVanishing (levelCharacter_sq)
open scoped MatrixGroups Topology

noncomputable section

def oddCosetPullback (f : OddSmoothCompactCore) (q : levelFourRightCoset) : ℂ → ℂ :=
  oddMaassPullback (cellRepresentative (CongruenceSubgroup.Gamma0 4) q) (f : ℂ → ℂ)

theorem oddCosetPullback_coe (f : OddSmoothCompactCore) (q : levelFourRightCoset) (z : ℍ) :
    oddCosetPullback f q z = oddCosetChart (f : ℂ → ℂ) q z :=
  oddMaassPullback_coe _ _ z

theorem oddCosetPullback_differentiableAt (f : OddSmoothCompactCore) (q : levelFourRightCoset) (z : ℍ) :
    DifferentiableAt ℝ (oddCosetPullback f q) (z : ℂ) :=
  oddMaassPullback_differentiableAt _ z (oddCore_differentiableAt f _)

private theorem maassCovariantEnergy_congr {F G : ℂ → ℂ} {z : ℍ} (hEq : F =ᶠ[𝓝 (z : ℂ)] G) :
    maassCovariantEnergy F z = maassCovariantEnergy G z := by
  unfold maassCovariantEnergy maassCovariantValue
  rw [hEq.fderiv_eq (𝕜 := ℝ), hEq.self_of_nhds]

private theorem maassCovariantEnergy_const_mul_unit {F : ℂ → ℂ} {z : ℍ}
    (hF : DifferentiableAt ℝ F (z : ℂ)) {c : ℂ} (hc : ‖c‖ = 1) :
    maassCovariantEnergy (fun w => c * F w) z = maassCovariantEnergy F z := by
  have hC (v : ℂ) : maassCovariantValue (fun w => c * F w) z v = c * maassCovariantValue F z v := by
    unfold maassCovariantValue
    rw [fderiv_const_mul hF]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  unfold maassCovariantEnergy
  simp only [hC, norm_mul, hc, one_mul]

theorem oddCosetPullback_energy_transform (f : OddSmoothCompactCore)
    (q : levelFourRightCoset) (g : SL(2, ℤ)) (z : ℍ) :
    maassCovariantEnergy (oddCosetPullback f q) (g • z) =
      maassCovariantEnergy (oddCosetPullback f (rightCosetMul (CongruenceSubgroup.Gamma0 4) g q)) z := by
  let r := rightCosetMul (CongruenceSubgroup.Gamma0 4) g q
  let h := levelFourChartTransition q g
  let χ : ℂ := (levelCharacter h : ℂ)
  have hSq : ‖χ‖ ^ 2 = 1 := by unfold χ; rw [← norm_pow, levelCharacter_sq, norm_one]
  have hχ : ‖χ‖ = 1 := by nlinarith [norm_nonneg χ]
  have hOpen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hEq : oddMaassPullback g (oddCosetPullback f q) =ᶠ[𝓝 (z : ℂ)]
      fun w => χ * oddCosetPullback f r w := by
    filter_upwards [hOpen.mem_nhds z.im_pos] with w hw
    let u : ℍ := ⟨w, hw⟩
    change oddMaassPullback g (oddCosetPullback f q) u = χ * oddCosetPullback f r u
    rw [oddMaassPullback_coe, oddCosetPullback_coe, oddCosetPullback_coe]
    have hT := oddCosetChart_transform f.2.1 q g u
    change oddCosetChart (f : ℂ → ℂ) q (g • u) =
      χ * negativePhase g u * oddCosetChart (f : ℂ → ℂ) r u at hT
    rw [hT]
    have hn : negativePhase g u ≠ 0 := by
      intro h0
      have hN := negativePhase_norm g u
      simp [h0] at hN
    field_simp [hn] <;> ring
  calc
    _ = maassCovariantEnergy (oddMaassPullback g (oddCosetPullback f q)) z :=
      (maassCovariantEnergy_pullback g z (oddCosetPullback_differentiableAt f q (g • z))).symm
    _ = maassCovariantEnergy (fun w => χ * oddCosetPullback f r w) z :=
      maassCovariantEnergy_congr hEq
    _ = _ := maassCovariantEnergy_const_mul_unit (oddCosetPullback_differentiableAt f r z) hχ

def oddCosetChartEnergyAt (f : OddSmoothCompactCore) (z : ℍ) : ℝ :=
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  ∑ q : levelFourRightCoset, maassCovariantEnergy (oddCosetPullback f q) z

theorem oddCosetChartEnergyAt_invariant (f : OddSmoothCompactCore) (g : SL(2, ℤ)) (z : ℍ) :
    oddCosetChartEnergyAt f (g • z) = oddCosetChartEnergyAt f z := by
  let H := CongruenceSubgroup.Gamma0 4
  letI := rightCosetFintype H
  unfold oddCosetChartEnergyAt
  refine Fintype.sum_equiv (rightCosetMul H g) _ _ (fun q => ?_)
  exact oddCosetPullback_energy_transform f q g z

theorem energy_oddCosetPullback (f : OddSmoothCompactCore) (q : levelFourRightCoset) (z : ℍ) :
    maassCovariantEnergy (oddCosetPullback f q) z =
      maassCovariantEnergy (f : ℂ → ℂ) (cellRepresentative (CongruenceSubgroup.Gamma0 4) q • z) :=
  maassCovariantEnergy_pullback _ z (oddCore_differentiableAt f _)

end
end ManuscriptAudit.Paper8OddCosetChartEnergy

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCosetChartEnergy.oddCosetChartEnergyAt_invariant
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
