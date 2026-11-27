import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSecantPoints

/-! Every algebraically closed abscissa occurs on the native cubic, with the two ordinates related by negation. -/

namespace ManuscriptAudit.CubicAbscissaFibers

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicThreeTorsionCard

noncomputable section
open scoped Classical

variable {L : Type*} [Field L] [DecidableEq L] {A : L}

/-- Two actual affine points with the same abscissa agree up to elliptic negation. -/
theorem same_abscissa_eq_or_neg (hΔ : (shortCubic (0 : L) A).Δ ≠ 0)
    {x y z : L} (hy : (Curve A).Nonsingular x y) (hz : (Curve A).Nonsingular x z) :
    (Affine.Point.some x z hz : (Curve A).Point) = .some x y hy ∨
      (Affine.Point.some x z hz : (Curve A).Point) = -(.some x y hy : (Curve A).Point) := by
  have hy' := (nonsingular_iff hΔ x y).mp hy
  have hz' := (nonsingular_iff hΔ x z).mp hz
  have h : (z - y) * (z + y) = 0 := by linear_combination hz' - hy'
  rcases mul_eq_zero.mp h with h | h
  · left
    rw [Affine.Point.some.injEq]
    exact ⟨rfl, sub_eq_zero.mp h⟩
  · right
    rw [Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, by
      have he : z = -y := eq_neg_of_add_eq_zero_left h
      simpa only [Curve, CubicAffine, shortCubic, Affine.negY, zero_mul, zero_add, sub_zero,
        neg_zero] using he⟩

variable [IsAlgClosed L]

/-- Choose a genuine affine point over any prescribed abscissa. -/
def pointWithX (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) (x : L) : (Curve A).Point :=
  let hs := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + A) (n := 2) (by decide)
  .some x (Classical.choose hs) ((nonsingular_iff hΔ x _).mpr (Classical.choose_spec hs))

theorem pointWithX_spec (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) (x : L) :
    ∃ (y : L) (hy : (Curve A).Nonsingular x y), pointWithX hΔ x = .some x y hy := ⟨_, _, rfl⟩

theorem abscissa_pointWithX (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) (x : L) :
    abscissa (pointWithX hΔ x) = x := rfl

/-- Over an algebraically closed field the actual group of points is infinite. -/
theorem infinite_points (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) : Infinite (Curve A).Point :=
  Infinite.of_surjective abscissa (fun x => ⟨pointWithX hΔ x, abscissa_pointWithX hΔ x⟩)

end

end ManuscriptAudit.CubicAbscissaFibers

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicAbscissaFibers.same_abscissa_eq_or_neg,
      ``ManuscriptAudit.CubicAbscissaFibers.pointWithX,
      ``ManuscriptAudit.CubicAbscissaFibers.pointWithX_spec,
      ``ManuscriptAudit.CubicAbscissaFibers.abscissa_pointWithX,
      ``ManuscriptAudit.CubicAbscissaFibers.infinite_points] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
