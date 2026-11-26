import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.NormNum

/-!
# The tensor target of the covariant derivative

Paper 10, physical page 492, equation (4.39). In dimension two the
half-turn acts trivially on the tensor square of the covector fiber and
by negation on the covector fiber itself. Thus no nonzero linear map
from the tensor square to one-forms commutes with all oriented
orthonormal frame changes. This rules out an intrinsic fiberwise
conversion before applying the paper's one-form projection, when
the conversion has no extra geometric input.
-/

namespace ManuscriptAudit.Paper10DerivativeTarget

open Matrix
open scoped TensorProduct Matrix

abbrev Covector := Fin 2 → ℝ
abbrev RealMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Equivariance under all oriented orthonormal frame changes of a plane. -/
def RespectsFrameChanges (T : (Covector ⊗[ℝ] Covector) →ₗ[ℝ] Covector) : Prop :=
  ∀ (g : RealMatrix), g.det = 1 → gᵀ * g = 1 →
    ∀ u v : Covector,
      T (g.mulVec u ⊗ₜ[ℝ] g.mulVec v) = g.mulVec (T (u ⊗ₜ[ℝ] v))

theorem halfTurn_is_oriented_orthogonal :
    (-1 : RealMatrix).det = 1 ∧ (-1 : RealMatrix)ᵀ * (-1 : RealMatrix) = 1 := by
  constructor
  · norm_num [Matrix.det_fin_two, Matrix.one_apply]
  · simp

theorem equivariant_tensor_to_covector_eq_zero
    (T : (Covector ⊗[ℝ] Covector) →ₗ[ℝ] Covector) (h : RespectsFrameChanges T) :
    T = 0 := by
  apply LinearMap.ext
  intro t
  change T t = 0
  refine TensorProduct.induction_on t (by simp) ?_ ?_
  · intro u v
    have he := h (-1) halfTurn_is_oriented_orthogonal.1 halfTurn_is_oriented_orthogonal.2 u v
    simp only [Matrix.neg_mulVec, Matrix.one_mulVec,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg] at he
    let x := T (u ⊗ₜ[ℝ] v)
    have hsum : x + x = 0 := by
      calc
        x + x = -x + x := congrArg (fun a : Covector => a + x) he
        _ = 0 := neg_add_cancel x
    have htwo : (2 : ℝ) • x = 0 := by simpa only [two_smul] using hsum
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · intro a b ha hb
    rw [map_add, ha, hb, zero_add]

end ManuscriptAudit.Paper10DerivativeTarget

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10DerivativeTarget.halfTurn_is_oriented_orthogonal,
      ``ManuscriptAudit.Paper10DerivativeTarget.equivariant_tensor_to_covector_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
