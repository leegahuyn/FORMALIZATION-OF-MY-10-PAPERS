import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Every point over an algebraic extension of a finite field has finite additive order. -/

namespace ManuscriptAudit.WeierstrassAlgebraicPointFiniteOrder

open WeierstrassCurve

noncomputable section

variable (E L : Type*) [Field E] [Finite E] [Field L] [Algebra E L]
  [Algebra.IsAlgebraic E L] [DecidableEq L]

/-- Both affine coordinates lie in a single actual finite extension. -/
theorem exists_positive_nsmul_eq_zero (W : Affine E) (P : (W.baseChange L).Point) :
    ∃ n : ℕ, 0 < n ∧ n • P = 0 := by
  classical
  cases P with
  | zero => exact ⟨1, Nat.one_pos, nsmul_zero _⟩
  | some x y hxy =>
    let K := IntermediateField.adjoin E ({x, y} : Set L)
    letI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin_pair
      (Algebra.IsIntegral.isIntegral (R := E) x) (Algebra.IsIntegral.isIntegral (R := E) y)
    letI : Finite K := Module.finite_of_finite E
    let i : K →ₐ[E] L := K.val
    let x₀ : K := ⟨x, IntermediateField.subset_adjoin E _ (by simp)⟩
    let y₀ : K := ⟨y, IntermediateField.subset_adjoin E _ (by simp)⟩
    have hx : i x₀ = x := rfl
    have hy : i y₀ = y := rfl
    have h₀ : (W.baseChange K).Nonsingular x₀ y₀ :=
      (W.baseChange_nonsingular (f := i) i.injective x₀ y₀).mp (by simpa only [hx, hy] using hxy)
    let Q : (W.baseChange K).Point := .some x₀ y₀ h₀
    let j := Affine.Point.map (W' := W) i
    have hQ : j Q = Affine.Point.some x y hxy := by
      change Affine.Point.map (W' := W) i (Affine.Point.some x₀ y₀ h₀) = _
      rw [Affine.Point.map_some, Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    let H := (W.baseChange K).Point
    letI : Finite (WithZero {xy : K × K // (W.baseChange K).Nonsingular xy.1 xy.2}) := by
      change Finite (Option {xy : K × K // (W.baseChange K).Nonsingular xy.1 xy.2})
      infer_instance
    letI : Finite H := Finite.of_injective _ (Affine.nonsingularPointEquiv (W.baseChange K)).injective
    refine ⟨Nat.card H, Nat.card_pos, ?_⟩
    calc
      _ = j ((Nat.card H) • Q) := by rw [map_nsmul, hQ]
      _ = 0 := by rw [card_nsmul_eq_zero', map_zero]

end
end ManuscriptAudit.WeierstrassAlgebraicPointFiniteOrder

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassAlgebraicPointFiniteOrder.exists_positive_nsmul_eq_zero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
