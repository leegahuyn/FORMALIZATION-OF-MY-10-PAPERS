import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HyperbolicCuspGaugeTest

/-! A locally bounded nonnegative cusp potential can make the printed energy form unbounded. -/

namespace ManuscriptAudit.Paper9CuspPotentialForm

open MeasureTheory HyperbolicCuspGaugeTest
open scoped ContDiff

noncomputable section

def heightPotential (y : ℝ) : ℝ := y ^ 6

theorem heightPotential_continuous : Continuous heightPotential :=
  continuous_id.pow 6

theorem heightPotential_negative_part (y : ℝ) : max (-heightPotential y) 0 = 0 :=
  max_eq_right (neg_nonpos.mpr (by unfold heightPotential; positivity))

def heightTest (Y y : ℝ) : ℝ := cuspBump (y - Y)

theorem heightTest_smooth (Y : ℝ) : ContDiff ℝ ∞ (heightTest Y) :=
  cuspBump_smooth.comp (contDiff_id.sub contDiff_const)

theorem heightTest_zero (Y y : ℝ) (h : y ≤ Y + 2 ∨ Y + 5 ≤ y) :
    heightTest Y y = 0 :=
  cuspBump_zero_of_height_outside (h.imp (by intro e; linarith) (by intro e; linarith))

theorem heightTest_deriv (Y y : ℝ) :
    deriv (heightTest Y) y = deriv cuspBump (y - Y) := by
  have h₁ := ((contDiff_infty.mp cuspBump_smooth 1).differentiable (by decide)
    (y - Y)).hasDerivAt
  have h₂ := (hasDerivAt_id y).sub_const Y
  simpa [heightTest, Function.comp_def] using (h₁.comp y h₂).deriv

/-- The three norm terms with the paper's raising and lowering formulas, times y⁻². -/
def energyDensity (Y t : ℝ) : ℝ :=
  (cuspBump t / (Y + t)) ^ 2 +
    (deriv cuspBump t / (Y + t) + cuspBump t / (2 * (Y + t) ^ 2)) ^ 2 +
    ((Y + t) * deriv cuspBump t) ^ 2

/-- The potential term with y⁻² and with y = Y + t. -/
def potentialDensity (Y t : ℝ) : ℝ :=
  (Y + t) ^ 4 * cuspBump t ^ 2

def energy (Y : ℝ) : ℝ := 2 * ∫ t : ℝ in (1 : ℝ)..6, energyDensity Y t

def potentialContribution (Y : ℝ) : ℝ :=
  2 * ∫ t : ℝ in (1 : ℝ)..6, potentialDensity Y t

def referenceEnergy : ℝ :=
  2 * ∫ t : ℝ in (1 : ℝ)..6, 3 * cuspBump t ^ 2 + 3 * deriv cuspBump t ^ 2

private theorem derivative_continuous : Continuous (deriv cuspBump) :=
  (contDiff_infty.mp cuspBump_smooth 1).continuous_deriv_one

private theorem div_sq_le_self (a b : ℝ) (hb : 1 ≤ b) :
    (a / b) ^ 2 ≤ a ^ 2 := by
  rw [div_pow]
  exact div_le_self (sq_nonneg a) (by nlinarith)

theorem energyDensity_le (Y t : ℝ) (hY : 1 ≤ Y) (ht : t ∈ Set.Icc (1 : ℝ) 6) :
    energyDensity Y t ≤ (Y + 6) ^ 2 * (3 * cuspBump t ^ 2 + 3 * deriv cuspBump t ^ 2) := by
  have h₁ : 1 ≤ Y + t := by linarith [ht.1]
  have h₂ : (Y + t) ^ 2 ≤ (Y + 6) ^ 2 := by
    exact pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
  have h₃ : 1 ≤ (Y + 6) ^ 2 := by nlinarith
  let a := cuspBump t
  let b := deriv cuspBump t
  have hR : (b / (Y + t) + a / (2 * (Y + t) ^ 2)) ^ 2 ≤ 2 * b ^ 2 + 2 * a ^ 2 := by
    have e₁ := div_sq_le_self b (Y + t) h₁
    have e₂ := div_sq_le_self a (2 * (Y + t) ^ 2) (by nlinarith)
    nlinarith [sq_nonneg (b / (Y + t) - a / (2 * (Y + t) ^ 2))]
  have hL : ((Y + t) * b) ^ 2 ≤ (Y + 6) ^ 2 * b ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right h₂ (sq_nonneg b)
  have hA := div_sq_le_self a (Y + t) h₁
  have hab : 0 ≤ 3 * a ^ 2 + 2 * b ^ 2 := by positivity
  have hab' := mul_le_mul_of_nonneg_right h₃ hab
  change (a / (Y + t)) ^ 2 + (b / (Y + t) + a / (2 * (Y + t) ^ 2)) ^ 2 +
    ((Y + t) * b) ^ 2 ≤ (Y + 6) ^ 2 * (3 * a ^ 2 + 3 * b ^ 2)
  nlinarith

private theorem energyDensity_continuousOn (Y : ℝ) (hY : 1 ≤ Y) :
    ContinuousOn (energyDensity Y) (Set.Icc (1 : ℝ) 6) := by
  have hB := cuspBump_smooth.continuous.continuousOn (s := Set.Icc (1 : ℝ) 6)
  have hD := derivative_continuous.continuousOn (s := Set.Icc (1 : ℝ) 6)
  have hH : ContinuousOn (fun t : ℝ => Y + t) (Set.Icc (1 : ℝ) 6) :=
    (continuous_const.add continuous_id).continuousOn
  have hn t (ht : t ∈ Set.Icc (1 : ℝ) 6) : Y + t ≠ 0 := by linarith [ht.1]
  have hnn t (ht : t ∈ Set.Icc (1 : ℝ) 6) : 2 * (Y + t) ^ 2 ≠ 0 := by
    positivity [hn t ht]
  exact (((hB.div hH hn).pow 2).add
    (((hD.div hH hn).add (hB.div (continuousOn_const.mul (hH.pow 2)) hnn)).pow 2)).add
    ((hH.mul hD).pow 2)

theorem energy_le (Y : ℝ) (hY : 1 ≤ Y) :
    energy Y ≤ (Y + 6) ^ 2 * referenceEnergy := by
  have hc : Continuous (fun t : ℝ => 3 * cuspBump t ^ 2 + 3 * deriv cuspBump t ^ 2) :=
    (continuous_const.mul (cuspBump_smooth.continuous.pow 2)).add
      (continuous_const.mul (derivative_continuous.pow 2))
  unfold energy referenceEnergy
  rw [← mul_assoc, mul_comm ((Y + 6) ^ 2) 2, mul_assoc, ← intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (energyDensity_continuousOn Y hY).intervalIntegrable_of_Icc (by norm_num)
  · exact (continuous_const.mul hc).intervalIntegrable 1 6
  · exact fun t ht => energyDensity_le Y t hY ht

theorem potential_ge (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ 4 * cuspMass ≤ potentialContribution Y := by
  have hB := cuspBump_smooth.continuous.pow (2 : ℕ)
  unfold cuspMass potentialContribution
  rw [← mul_assoc, mul_comm (Y ^ 4) 2, mul_assoc, ← intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (continuous_const.mul hB).intervalIntegrable 1 6
  · exact (((continuous_const.add continuous_id).pow 4).mul hB).intervalIntegrable 1 6
  · intro t ht
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith [ht.1]) 4)
      (sq_nonneg (cuspBump t))

private theorem referenceEnergy_nonneg : 0 ≤ referenceEnergy := by
  unfold referenceEnergy
  apply mul_nonneg (by norm_num)
  exact intervalIntegral.integral_nonneg (by norm_num) (by intro t ht; positivity)

theorem no_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ Y : ℝ, 1 ≤ Y ∧ C * energy Y < potentialContribution Y := by
  let A := 4 * C * referenceEnergy
  let Y := 7 + A / cuspMass
  have hA : 0 ≤ A := by unfold A; positivity [referenceEnergy_nonneg]
  have hY : 7 ≤ Y := le_add_of_nonneg_right (div_nonneg hA cuspMass_pos.le)
  have hYm : Y * cuspMass = 7 * cuspMass + A := by
    dsimp [Y]
    field_simp [cuspMass_pos.ne'] <;> ring
  have hYY : A < Y ^ 2 * cuspMass := by
    have he : Y ≤ Y ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right he cuspMass_pos.le
    linarith
  have hh : (Y + 6) ^ 2 ≤ 4 * Y ^ 2 := by nlinarith
  have hm : 0 ≤ C * referenceEnergy := mul_nonneg hC referenceEnergy_nonneg
  refine ⟨Y, by linarith, (mul_le_mul_of_nonneg_left (energy_le Y (by linarith)) hC).trans_lt ?_⟩
  calc
    C * ((Y + 6) ^ 2 * referenceEnergy) ≤ Y ^ 2 * A := by
      have h := mul_le_mul_of_nonneg_right hh hm
      dsimp [A]
      nlinarith only [h]
    _ < Y ^ 4 * cuspMass := by
      have h := mul_lt_mul_of_pos_left hYY (sq_pos_of_pos (by linarith : 0 < Y))
      convert h using 1 <;> ring
    _ ≤ potentialContribution Y := potential_ge Y (by linarith)

end
end ManuscriptAudit.Paper9CuspPotentialForm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspPotentialForm.heightPotential_continuous,
      ``ManuscriptAudit.Paper9CuspPotentialForm.heightPotential_negative_part,
      ``ManuscriptAudit.Paper9CuspPotentialForm.heightTest_smooth,
      ``ManuscriptAudit.Paper9CuspPotentialForm.heightTest_zero,
      ``ManuscriptAudit.Paper9CuspPotentialForm.heightTest_deriv,
      ``ManuscriptAudit.Paper9CuspPotentialForm.energy_le,
      ``ManuscriptAudit.Paper9CuspPotentialForm.potential_ge,
      ``ManuscriptAudit.Paper9CuspPotentialForm.no_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
