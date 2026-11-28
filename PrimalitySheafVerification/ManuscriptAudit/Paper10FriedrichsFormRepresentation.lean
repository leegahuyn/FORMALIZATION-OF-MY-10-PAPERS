import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsShift
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeFormBounds

/-! The actual shifted-back operator realizes the relative form and has the
form's quantitative bound. -/

namespace ManuscriptAudit.Paper10FriedrichsFormRepresentation

open Paper10FriedrichsResolvent Paper10FriedrichsShift
open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (J : D →L[ℝ] H) (hJ : DenseRange J) (c : ℝ)
variable (q v : D → ℝ)
variable (hNorm : ∀ u, ‖u‖ ^ 2 = q u + v u + c * ‖J u‖ ^ 2)

include hNorm in
/-- The actual partial operator gives precisely the form's diagonal on its domain. -/
theorem form_value {x y : H} (hxy : (x,y) ∈ (unshifted J c).graph) :
    ∃ u : D, J u = x ∧ ⟪y,x⟫ = q u + v u := by
  have h := (unshifted_graph_iff J c x y).mp hxy
  obtain ⟨u, hu, hv⟩ := (realization_form_iff J hJ x (y+c • x)).mp h
  have he := hv u
  rw [real_inner_self_eq_norm_sq, hu, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at he
  have hn := hNorm u
  rw [hu] at hn
  exact ⟨u, hu, by linarith only [he, hn]⟩

include hNorm in
/-- The relative perturbation's lower bound holds on the actual operator graph. -/
theorem graph_lower_bound (m a b : ℝ) (ha : a < 1)
    (hq : ∀ u, -m * ‖J u‖ ^ 2 ≤ q u) (hv : ∀ u, |v u| ≤ a*q u+b*‖J u‖^2)
    {x y : H} (hxy : (x,y) ∈ (unshifted J c).graph) :
    -((1-a)*m+b) * ‖x‖ ^ 2 ≤ ⟪y,x⟫ := by
  obtain ⟨u, hu, he⟩ := form_value J hJ c q v hNorm hxy
  rw [← hu, he]
  exact Paper10RelativeFormBounds.semibounded q v (fun u => ‖J u‖^2) m a b ha hq hv u

end
end ManuscriptAudit.Paper10FriedrichsFormRepresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsFormRepresentation.form_value,
      ``ManuscriptAudit.Paper10FriedrichsFormRepresentation.graph_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
