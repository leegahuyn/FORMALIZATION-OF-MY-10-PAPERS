import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! The variational inverse defined by the adjoint of a dense energy-space inclusion. -/

namespace ManuscriptAudit.Paper8EnergyFormResolvent

open scoped InnerProductSpace

noncomputable section

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def energyFormResolvent (J : V →L[ℂ] H) : H →L[ℂ] H :=
  J.comp J.adjoint

theorem energyFormResolvent_variational (J : V →L[ℂ] H) (f : H) (v : V) :
    ⟪v, J.adjoint f⟫_ℂ = ⟪J v, f⟫_ℂ :=
  J.adjoint_inner_right v f

theorem energyFormResolvent_symmetric (J : V →L[ℂ] H) :
    (energyFormResolvent J).IsSymmetric := by
  have hAdj : energyFormResolvent J = (energyFormResolvent J).adjoint := by
    simp only [energyFormResolvent, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).1 hAdj

theorem energyFormResolvent_nonnegative (J : V →L[ℂ] H) (f : H) :
    0 ≤ (⟪f, energyFormResolvent J f⟫_ℂ).re := by
  change 0 ≤ (⟪f, J (J.adjoint f)⟫_ℂ).re
  rw [← J.adjoint_inner_left]
  change 0 ≤ RCLike.re ⟪J.adjoint f, J.adjoint f⟫_ℂ
  rw [inner_self_eq_norm_sq]
  exact sq_nonneg _

theorem energyFormResolvent_injective (J : V →L[ℂ] H)
    (hDense : J.range.topologicalClosure = ⊤) : Function.Injective (energyFormResolvent J) := by
  have hOrtho : J.rangeᗮ = ⊥ := Submodule.topologicalClosure_eq_top_iff.mp hDense
  have hKer : (energyFormResolvent J).ker = ⊥ := by
    rw [energyFormResolvent, J.ker_self_comp_adjoint, ← J.orthogonal_range, hOrtho]
  exact LinearMap.ker_eq_bot.mp hKer

theorem energyFormResolvent_compact (J : V →L[ℂ] H) (hCompact : IsCompactOperator J) :
    IsCompactOperator (energyFormResolvent J) :=
  hCompact.comp_clm J.adjoint

end
end ManuscriptAudit.Paper8EnergyFormResolvent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EnergyFormResolvent.energyFormResolvent_variational,
      ``ManuscriptAudit.Paper8EnergyFormResolvent.energyFormResolvent_injective,
      ``ManuscriptAudit.Paper8EnergyFormResolvent.energyFormResolvent_compact] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
