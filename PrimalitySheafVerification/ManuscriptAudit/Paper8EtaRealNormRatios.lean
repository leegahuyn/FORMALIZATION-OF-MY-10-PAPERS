import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaBaselineMass
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCosetBoundary

/-! The actual positive real eta masses and their reciprocal ratios at levels one, two and four. -/

namespace ManuscriptAudit.Paper8EtaRealNormRatios

open Set MeasureTheory UpperHalfPlane
open Paper8EtaPeterssonMass Paper8EtaCosetMass Paper8EtaCosetBoundary Paper8EtaBaselineMass
open scoped ENNReal MatrixGroups

noncomputable section

private theorem mass_congr_ae {S T : Set ℍ} (h : S =ᵐ[(volume : Measure ℍ)] T) :
    mass S = mass T := by
  unfold mass
  rw [Measure.restrict_congr_set h]

theorem mass_closed_eq_open :
    mass ModularGroup.fd = mass ModularGroup.fdo := by
  apply mass_congr_ae
  exact ae_eq_set.mpr ⟨volume_fd_boundary_zero,
    by simp [sdiff_eq_empty.mpr ModularGroup.fdo_subset_fd]⟩

theorem mass_closed_cells_eq_open (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    mass (cosetCells H ModularGroup.fd) = mass (cosetCells H ModularGroup.fdo) :=
  mass_congr_ae (closed_cells_ae_eq_open H)

def levelTwo : ℝ :=
  (mass (cosetCells (CongruenceSubgroup.Gamma0 2) ModularGroup.fdo)).toReal

def levelFour : ℝ :=
  (mass (cosetCells (CongruenceSubgroup.Gamma0 4) ModularGroup.fdo)).toReal

theorem levelTwo_eq_three_mul : levelTwo = 3 * baseline := by
  unfold levelTwo baseline
  rw [levelTwo_eta_mass, ENNReal.toReal_mul]
  norm_num

theorem levelFour_eq_six_mul : levelFour = 6 * baseline := by
  unfold levelFour baseline
  rw [levelFour_eta_mass, ENNReal.toReal_mul]
  norm_num

theorem level_masses_pos : 0 < levelTwo ∧ 0 < levelFour := by
  rw [levelTwo_eq_three_mul, levelFour_eq_six_mul]
  exact ⟨mul_pos (by norm_num) baseline_pos, mul_pos (by norm_num) baseline_pos⟩

theorem level_ratios :
    levelTwo / baseline = 3 ∧ levelFour / baseline = 6 ∧ levelFour / levelTwo = 2 := by
  rw [levelTwo_eq_three_mul, levelFour_eq_six_mul]
  constructor
  · field_simp [baseline_pos.ne']
  constructor
  · field_simp [baseline_pos.ne']
  · field_simp [baseline_pos.ne']
    <;> ring

theorem reciprocal_level_ratios :
    levelTwo⁻¹ = baseline⁻¹ / 3 ∧ levelFour⁻¹ = baseline⁻¹ / 6 := by
  rw [levelTwo_eq_three_mul, levelFour_eq_six_mul]
  constructor
  · field_simp [baseline_pos.ne']
    <;> ring
  · field_simp [baseline_pos.ne']
    <;> ring

end
end ManuscriptAudit.Paper8EtaRealNormRatios

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaRealNormRatios.mass_closed_eq_open,
      ``ManuscriptAudit.Paper8EtaRealNormRatios.mass_closed_cells_eq_open,
      ``ManuscriptAudit.Paper8EtaRealNormRatios.levelTwo_eq_three_mul,
      ``ManuscriptAudit.Paper8EtaRealNormRatios.levelFour_eq_six_mul,
      ``ManuscriptAudit.Paper8EtaRealNormRatios.level_masses_pos,
      ``ManuscriptAudit.Paper8EtaRealNormRatios.level_ratios,
      ``ManuscriptAudit.Paper8EtaRealNormRatios.reciprocal_level_ratios] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
