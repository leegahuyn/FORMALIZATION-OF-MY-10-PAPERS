import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The first variation and the dual-metric norm in a scalar mode

Paper 10, p. 488, derives a dissipation identity by pairing the first
variation with the time derivative. In a scalar pivot space with
H¹ norm √2·|a|, the dual norm of the functional v is |v|/√2.
The smooth mode below satisfies the pivot evolution and the first
variation identity. The resulting dissipation rates are different.
-/

namespace ManuscriptAudit.EnergyDissipationModal

def mode (t : ℝ) : ℝ := Real.exp (-2 * t)

def energy (a : ℝ) : ℝ := a ^ 2

def firstVariation (a : ℝ) : ℝ := 2 * a

theorem modal_dual_norm_isLeast (v : ℝ) :
    IsLeast {C : ℝ | ∀ a : ℝ, |v * a| ≤ C * (Real.sqrt 2 * |a|)}
      (|v| / Real.sqrt 2) := by
  have h : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨?_, ?_⟩
  · intro a
    apply le_of_eq
    rw [abs_mul]
    field_simp [h.ne'] <;> ring
  · intro C hC
    exact (div_le_iff₀ h).2 (by simpa using hC 1)

theorem modal_dual_norm_sq (v : ℝ) :
    (|v| / Real.sqrt 2) ^ 2 = v ^ 2 / 2 := by
  rw [div_pow, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem modal_first_variation (a v : ℝ) :
    HasDerivAt (fun ε => energy (a + ε * v)) (firstVariation a * v) 0 := by
  have h : HasDerivAt (fun ε : ℝ => a + ε * v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add a
  convert h.pow 2 using 1 <;> simp [energy, firstVariation] <;> ring

theorem modal_flow_equation (t : ℝ) :
    HasDerivAt mode (-firstVariation (mode t)) t := by
  have hLin : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
  convert (Real.hasDerivAt_exp (-2 * t)).comp t hLin using 1 <;>
    unfold mode firstVariation <;> ring

theorem modal_energy_derivative (t : ℝ) :
    HasDerivAt (fun s => energy (mode s)) (-4 * (mode t) ^ 2) t := by
  convert (modal_flow_equation t).pow 2 using 1 <;>
    simp [energy, firstVariation] <;> ring

/-- The first-variation evolution can be smooth and still fail the
dissipation rate obtained by replacing its pairing by the dual norm. -/
theorem paper10_modal_energy_derivative_ne_negative_dual_norm (t : ℝ) :
    deriv (fun s => energy (mode s)) t ≠ -((|firstVariation (mode t)| / Real.sqrt 2) ^ 2) := by
  rw [(modal_energy_derivative t).deriv, modal_dual_norm_sq]
  intro h
  have hp : 0 < (mode t) ^ 2 := pow_pos (Real.exp_pos _) 2
  dsimp [firstVariation] at h
  nlinarith

end ManuscriptAudit.EnergyDissipationModal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.EnergyDissipationModal.modal_dual_norm_isLeast,
      ``ManuscriptAudit.EnergyDissipationModal.modal_dual_norm_sq,
      ``ManuscriptAudit.EnergyDissipationModal.modal_first_variation,
      ``ManuscriptAudit.EnergyDissipationModal.modal_flow_equation,
      ``ManuscriptAudit.EnergyDissipationModal.modal_energy_derivative,
      ``ManuscriptAudit.EnergyDissipationModal.paper10_modal_energy_derivative_ne_negative_dual_norm] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
