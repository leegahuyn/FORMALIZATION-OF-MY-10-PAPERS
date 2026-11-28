import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsResolvent

/-! Removing a real form shift from the actual positive realization preserves
self-adjointness and gives the exact lower bound. -/

namespace ManuscriptAudit.Paper10FriedrichsShift

open Paper10FriedrichsResolvent
open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (J : D →L[ℝ] H) (c : ℝ)

/-- Subtract the scalar shift on the original unbounded domain. -/
def unshifted : H →ₗ.[ℝ] H :=
  ⟨(realization J).domain, (realization J).toFun - c • (realization J).domain.subtype⟩

/-- The graph identifies the exact shifted value on every vector of the domain. -/
theorem unshifted_graph_iff (x y : H) :
    (x,y) ∈ (unshifted J c).graph ↔ (x,y+c • x) ∈ (realization J).graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨t, ht, hy⟩
    change (t : H) = x at ht
    refine ⟨t, ht, ?_⟩
    change (realization J) t - c • (t : H) = y at hy
    change (realization J) t = y + c • x
    rw [← ht, ← hy, sub_add_cancel]
  · rintro ⟨t, ht, hy⟩
    change (t : H) = x at ht
    change (realization J) t = y + c • x at hy
    refine ⟨t, ht, ?_⟩
    change (realization J) t - c • (t : H) = y
    rw [hy, ht, add_sub_cancel_right]

theorem unshifted_selfAdjoint (hJ : DenseRange J) : IsSelfAdjoint (unshifted J c) := by
  let A := realization J
  have hA : IsSelfAdjoint A := realization_selfAdjoint J hJ
  have hAdj : A.graph.adjoint = A.graph := by
    rw [← LinearPMap.adjoint_graph_eq_graph_adjoint hA.dense_domain,
      LinearPMap.isSelfAdjoint_def.mp hA]
  have hDense : Dense ((unshifted J c).domain : Set H) := hA.dense_domain
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hDense]
  ext p
  rcases p with ⟨x,y⟩
  rw [Submodule.mem_adjoint_iff, unshifted_graph_iff]
  constructor
  · intro h
    have hxy : (x,y+c • x) ∈ A.graph.adjoint := by
      apply (Submodule.mem_adjoint_iff _ _).mpr
      intro a b hb
      have hb' : (a,b-c • a) ∈ (unshifted J c).graph :=
        (unshifted_graph_iff J c a (b-c • a)).mpr (by rwa [sub_add_cancel])
      have he := sub_eq_zero.mp (h a (b-c • a) hb')
      change ⟪b-c • a,x⟫ = ⟪a,y⟫ at he
      change ⟪b,x⟫ - ⟪a,y+c • x⟫ = 0
      rw [inner_sub_left, real_inner_smul_left] at he
      rw [inner_add_right, real_inner_smul_right]
      linarith only [he]
    exact hAdj ▸ hxy
  · intro h a b hb
    have hxy : (x,y+c • x) ∈ A.graph.adjoint := hAdj.symm ▸ h
    have hb' : (a,b+c • a) ∈ A.graph := (unshifted_graph_iff J c a b).mp hb
    have he := sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp hxy a (b+c • a) hb')
    change ⟪b+c • a,x⟫ = ⟪a,y+c • x⟫ at he
    change ⟪b,x⟫ - ⟪a,y⟫ = 0
    rw [inner_add_left, real_inner_smul_left, inner_add_right, real_inner_smul_right] at he
    linarith only [he]

/-- The actual shifted-back Hamiltonian is bounded below by the negative shift. -/
theorem unshifted_lower_bound (hJ : DenseRange J) {x y : H}
    (h : (x,y) ∈ (unshifted J c).graph) : -c * ‖x‖ ^ 2 ≤ ⟪y,x⟫ := by
  let f := y+c • x
  have hx : resolvent J f = x := (realization_graph_iff J hJ x f).mp
    ((unshifted_graph_iff J c x y).mp h)
  have hp : 0 ≤ ⟪f,x⟫ := by
    rw [← hx]
    change 0 ≤ ⟪f, J (J.adjoint f)⟫
    rw [← J.adjoint_inner_left, real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  change 0 ≤ ⟪y+c • x,x⟫ at hp
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hp
  linarith only [hp]

end
end ManuscriptAudit.Paper10FriedrichsShift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsShift.unshifted_graph_iff,
      ``ManuscriptAudit.Paper10FriedrichsShift.unshifted_selfAdjoint,
      ``ManuscriptAudit.Paper10FriedrichsShift.unshifted_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
