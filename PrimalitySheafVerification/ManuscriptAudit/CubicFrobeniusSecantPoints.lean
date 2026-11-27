import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSumNumerator
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace

/-! The rational sum and difference formulas evaluate on the actual native affine point group. -/

namespace ManuscriptAudit.CubicFrobeniusSecantPoints

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace
open CubicFrobeniusDifferenceNumerator CubicFrobeniusSumNumerator

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [Field L] [DecidableEq L] [Algebra K L]

theorem actual_frobenius_some (A : K) (x y : L)
    (hP : (Curve (algebraMap K L A)).Nonsingular x y) :
    ∃ hF : (Curve (algebraMap K L A)).Nonsingular (x ^ Fintype.card K) (y ^ Fintype.card K),
      arithmeticPointFrobenius K L A (.some x y hP) =
        .some (x ^ Fintype.card K) (y ^ Fintype.card K) hF :=
  pointMapAt_some K L (Curve A) (Curve (algebraMap K L A))
    (centered_baseChange K L A) (FiniteField.frobeniusAlgHom K L) x y hP

private theorem negY_formula (A : K) (x y : L) : (Curve (algebraMap K L A)).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

/-- Both rational functions describe exactly the native xRep coordinates of F(P)±P. -/
theorem secant_xRep {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (A : K)
    (x y : L) (hP : (Curve (algebraMap K L A)).Nonsingular x y)
    (h : y ^ 2 = x ^ 3 + algebraMap K L A) (hx : x ^ Fintype.card K ≠ x) :
    let F := arithmeticPointFrobenius K L A
    let P : GeometricPoints K L A := .some x y hP
    let D := (x ^ Fintype.card K - x) ^ 2
    (F P + P).xRep = ![(sumNumerator (Fintype.card K) k (algebraMap K L A)).eval x / D, 1] ∧
    (F P - P).xRep = ![(numerator (Fintype.card K) k (algebraMap K L A)).eval x / D, 1] := by
  obtain ⟨hF, hf⟩ := actual_frobenius_some K L A x y hP
  obtain ⟨hPlus, hMinus⟩ := secant_ratios K L hq A x y h hx
  dsimp only
  rw [hf]
  constructor
  · rw [Affine.Point.add_of_X_ne hx, Affine.Point.xRep_some, Affine.slope_of_X_ne hx]
    have hX : (Curve (algebraMap K L A)).addX (x ^ Fintype.card K) x
        ((y ^ Fintype.card K - y) / (x ^ Fintype.card K - x)) =
        (sumNumerator (Fintype.card K) k (algebraMap K L A)).eval x /
          (x ^ Fintype.card K - x) ^ 2 := by
      simpa [Curve, CubicAffine, shortCubic, Affine.addX] using hPlus
    rw [hX]
  · rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx,
      Affine.Point.xRep_some, Affine.slope_of_X_ne hx, negY_formula]
    have hX : (Curve (algebraMap K L A)).addX (x ^ Fintype.card K) x
        ((y ^ Fintype.card K + y) / (x ^ Fintype.card K - x)) =
        (numerator (Fintype.card K) k (algebraMap K L A)).eval x /
          (x ^ Fintype.card K - x) ^ 2 := by
      simpa [Curve, CubicAffine, shortCubic, Affine.addX] using hMinus
    rw [sub_neg_eq_add, hX]

end

end ManuscriptAudit.CubicFrobeniusSecantPoints

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusSecantPoints.actual_frobenius_some,
      ``ManuscriptAudit.CubicFrobeniusSecantPoints.secant_xRep] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
