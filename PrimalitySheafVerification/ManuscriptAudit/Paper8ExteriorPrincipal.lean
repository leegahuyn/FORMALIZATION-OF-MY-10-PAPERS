import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplexHolomorphy

/-!
# The actual principal exterior normalization in Paper 8

On the slit plane the printed factor at the reciprocal argument equals the
principal twenty-fourth root of the inverted argument. The weighted exterior
series is holomorphic on that complex domain.
-/

namespace ManuscriptAudit.Paper8ExteriorPrincipal

open Set Paper8InsideComplexAnalytic Paper8ExteriorComplex Paper8ExteriorComplexHolomorphy

noncomputable section

def principalRoot (q : ℂ) : ℂ := q ^ (24 : ℂ)⁻¹

def principalNormalization (q : ℂ) : ℂ := principalRoot q * exterior q

theorem principalRoot_pow (q : ℂ) : principalRoot q ^ (24 : ℕ) = q := by
  unfold principalRoot
  exact Complex.cpow_nat_inv_pow q (by decide : (24 : ℕ) ≠ 0)

theorem principal_normalization_eq_literal {q : ℂ} (hSlit : q ∈ Complex.slitPlane) (hq : ‖q‖ < 1) :
    principalNormalization q = (q⁻¹) ^ (-((24 : ℂ)⁻¹)) * standard q⁻¹ := by
  rw [principalNormalization, principalRoot,
    Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi hSlit), Complex.cpow_neg, inv_inv,
    standard_inv_eq_exterior (Complex.slitPlane_ne_zero hSlit) hq]

theorem principal_literal_absolute_summability {q : ℂ}
    (hSlit : q ∈ Complex.slitPlane) (hq : ‖q‖ < 1) :
    Summable (fun n => ‖(q⁻¹) ^ (-((24 : ℂ)⁻¹)) * standardTerm n q⁻¹‖) := by
  simpa only [norm_mul] using (absolute_summability_at_inverse
    (Complex.slitPlane_ne_zero hSlit) hq).mul_left ‖(q⁻¹) ^ (-((24 : ℂ)⁻¹))‖

theorem principalNormalization_differentiableOn :
    DifferentiableOn ℂ principalNormalization (Metric.ball (0 : ℂ) 1 ∩ Complex.slitPlane) := by
  have hRoot : DifferentiableOn ℂ principalRoot (Metric.ball (0 : ℂ) 1 ∩ Complex.slitPlane) :=
    differentiableOn_id.cpow_const (fun _ hq => hq.2)
  exact hRoot.mul (exterior_differentiableOn_unit_disk.mono Set.inter_subset_left)

theorem principal_literal_differentiableOn_exterior :
    DifferentiableOn ℂ (fun z : ℂ => z ^ (-((24 : ℂ)⁻¹)) * standard z)
      ({z : ℂ | 1 < ‖z‖} ∩ Complex.slitPlane) := by
  have hWeight : DifferentiableOn ℂ (fun z : ℂ => z ^ (-((24 : ℂ)⁻¹)))
      ({z : ℂ | 1 < ‖z‖} ∩ Complex.slitPlane) :=
    differentiableOn_id.cpow_const (fun _ hz => hz.2)
  exact hWeight.mul (standard_differentiableOn_exterior.mono Set.inter_subset_left)

end
end ManuscriptAudit.Paper8ExteriorPrincipal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorPrincipal.principalRoot_pow,
      ``ManuscriptAudit.Paper8ExteriorPrincipal.principal_normalization_eq_literal,
      ``ManuscriptAudit.Paper8ExteriorPrincipal.principal_literal_absolute_summability,
      ``ManuscriptAudit.Paper8ExteriorPrincipal.principalNormalization_differentiableOn,
      ``ManuscriptAudit.Paper8ExteriorPrincipal.principal_literal_differentiableOn_exterior] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
