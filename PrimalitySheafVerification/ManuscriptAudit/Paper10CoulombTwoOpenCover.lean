import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombPartition

/-! A proper two-open cover on the periodic cusp admits no subordinate Coulomb localization of the test. -/

namespace ManuscriptAudit.Paper10CoulombTwoOpenCover

open Paper10CoulombPartition Paper10CoulombMultiplier Paper10CoulombProductRule
open scoped ContDiff BigOperators

noncomputable section

def angularCoordinate (x : ℝ) : ℝ := Real.cos (Real.pi*x)

def leftArc : Set ℝ := {x | angularCoordinate x < 1/2}

def rightArc : Set ℝ := {x | -(1/2 : ℝ) < angularCoordinate x}

theorem open_cover :
    IsOpen leftArc ∧ IsOpen rightArc ∧ leftArc ∪ rightArc = Set.univ := by
  have h : Continuous angularCoordinate :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  refine ⟨isOpen_lt h continuous_const, isOpen_lt continuous_const h, ?_⟩
  ext x
  simp only [leftArc, rightArc, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  by_cases hx : angularCoordinate x < 1/2
  · exact Or.inl hx
  · exact Or.inr (by linarith)

theorem angularCoordinate_periodic (x : ℝ) (m : ℤ) :
    angularCoordinate (x+2*(m : ℝ)) = angularCoordinate x := by
  unfold angularCoordinate
  rw [show Real.pi*(x+2*(m : ℝ)) = Real.pi*x + (m : ℝ)*(2*Real.pi) by ring,
    Real.cos_add_int_mul_two_pi]

def arc (i : Bool) : Set ℝ := if i then leftArc else rightArc

def leftWeight (x : ℝ) : ℝ := Real.smoothTransition (1/2 - 2*angularCoordinate x)

def weight (i : Bool) : ScalarField :=
  fun x _ => if i then leftWeight x else 1-leftWeight x

theorem actual_weights_smooth (i : Bool) :
    ContDiff ℝ ∞ (Function.uncurry (weight i)) := by
  have h₁ : ContDiff ℝ ∞ (fun p : ℝ×ℝ => Real.pi*p.1) :=
    contDiff_const.mul contDiff_fst
  have hC : ContDiff ℝ ∞ (fun p : ℝ×ℝ => angularCoordinate p.1) := Real.contDiff_cos.comp h₁
  have hA : ContDiff ℝ ∞ (fun p : ℝ×ℝ => (1/2 : ℝ)-2*angularCoordinate p.1) :=
    contDiff_const.sub (contDiff_const.mul hC)
  have hL : ContDiff ℝ ∞ (fun p : ℝ×ℝ => leftWeight p.1) :=
    Real.smoothTransition.contDiff.comp hA
  cases i
  · change ContDiff ℝ ∞ (fun x : ℝ×ℝ => 1 - leftWeight x.1)
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ×ℝ => (1 : ℝ))).sub hL
  · change ContDiff ℝ ∞ (fun x : ℝ×ℝ => leftWeight x.1)
    exact hL

theorem arcs_and_weights_periodic (i : Bool) (x y : ℝ) (m : ℤ) :
    (x+2*(m : ℝ) ∈ arc i ↔ x ∈ arc i) ∧ weight i (x+2*(m : ℝ)) y = weight i x y := by
  cases i <;> simp [arc, leftArc, rightArc, weight, leftWeight, angularCoordinate_periodic]

theorem explicit_partition (x y : ℝ) :
    (∀ i, 0 ≤ weight i x y) ∧ (∑ i, weight i x y) = 1 ∧
      (∀ i, x ∉ arc i → weight i x y = 0) := by
  have h₀ : 0 ≤ leftWeight x := Real.smoothTransition.nonneg _
  have h₁ : leftWeight x ≤ 1 := Real.smoothTransition.le_one _
  refine ⟨?_, ?_, ?_⟩
  · intro i
    cases i <;> simp [weight, h₀, sub_nonneg.mpr h₁]
  · simp [weight]
  · intro i
    cases i
    · simp only [arc, Bool.false_eq_true, if_false, rightArc, Set.mem_setOf_eq, not_lt, weight]
      intro hx
      rw [leftWeight, Real.smoothTransition.one_of_one_le (by linarith), sub_self]
    · simp only [arc, if_true, leftArc, Set.mem_setOf_eq, not_lt, weight]
      intro hx
      exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem no_subordinate_partition_keeps_coulomb (χ : Bool → ScalarField)
    (hDiff : ∀ i, Differentiable ℝ (fun x => χ i x 3))
    (hSum : ∀ x, ∑ i, χ i x 3 = 1)
    (hSub : ∀ i x, x ∉ arc i → χ i x 3 = 0) :
    ∃ i x, codifferential (scaleOneForm (χ i) witnessForm) x 3 ≠ 0 := by
  apply some_partition_piece_leaves_slice χ hDiff _ hSum
  intro i
  cases i
  · refine ⟨1, hSub false 1 ?_⟩
    norm_num [arc, rightArc, angularCoordinate, Real.cos_pi]
  · refine ⟨0, hSub true 0 ?_⟩
    norm_num [arc, leftArc, angularCoordinate]

end
end ManuscriptAudit.Paper10CoulombTwoOpenCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CoulombTwoOpenCover.open_cover,
      ``ManuscriptAudit.Paper10CoulombTwoOpenCover.angularCoordinate_periodic,
      ``ManuscriptAudit.Paper10CoulombTwoOpenCover.actual_weights_smooth,
      ``ManuscriptAudit.Paper10CoulombTwoOpenCover.arcs_and_weights_periodic,
      ``ManuscriptAudit.Paper10CoulombTwoOpenCover.explicit_partition,
      ``ManuscriptAudit.Paper10CoulombTwoOpenCover.no_subordinate_partition_keeps_coulomb] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
