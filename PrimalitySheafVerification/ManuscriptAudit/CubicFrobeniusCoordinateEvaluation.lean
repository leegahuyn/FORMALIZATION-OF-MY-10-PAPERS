import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RationalSubstitutionDegree
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSumNumerator
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceDegree

/-! The actual one-variable Frobenius secant functions commute with rational substitution. -/

namespace ManuscriptAudit.CubicFrobeniusCoordinateEvaluation

open Polynomial RationalSubstitutionDegree
open CubicFrobeniusDifferenceNumerator CubicFrobeniusSumNumerator
open CubicFrobeniusDifferenceGCD CubicFrobeniusDifferenceDegree

noncomputable section

variable {K : Type*} [Field K] [Fintype K]

/-- The normalized abscissa of F(P)+P as a rational function of the input abscissa. -/
def sumCoordinate (k : ℕ) (A : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (sumNumerator (Fintype.card K) k A) /
    ((RatFunc.X : RatFunc K) ^ Fintype.card K - RatFunc.X) ^ 2

theorem diffCoordinate_eq (k : ℕ) (A : K) :
    coordinate K k A =
      algebraMap K[X] (RatFunc K) (numerator (Fintype.card K) k A) /
        ((RatFunc.X : RatFunc K) ^ Fintype.card K - RatFunc.X) ^ 2 := by
  rw [coordinate, denominator, map_pow, map_sub, map_pow, RatFunc.algebraMap_X]

/-- A nonconstant input cannot be fixed by the power map of a finite base field. -/
theorem power_ne_of_nonconstant (r : RatFunc K) (hr : ¬ ∃ c : K, r = RatFunc.C c) :
    r ^ Fintype.card K ≠ r := by
  have hD : ((X : K[X]) ^ Fintype.card K - X) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hMap := RatFunc.algebraMap_ne_zero hD
  have h := (map_ne_zero (substitute r hr)).mpr hMap
  apply sub_ne_zero.mp
  simpa only [map_sub, map_pow, RatFunc.algebraMap_X, substitute_X] using h

private theorem substitute_ratio (r : RatFunc K) (hr : ¬ ∃ c : K, r = RatFunc.C c)
    (f : Polynomial K) :
    substitute r hr (algebraMap K[X] (RatFunc K) f /
      ((RatFunc.X : RatFunc K) ^ Fintype.card K - RatFunc.X) ^ 2) =
      aeval r f / (r ^ Fintype.card K - r) ^ 2 := by
  rw [map_div₀, substitute_algebraMap, map_pow, map_sub, map_pow, substitute_X]

variable (L : Type*) [Field L] [Algebra K L] [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]

/-- Both actual secant evaluations are the corresponding rational substitutions. -/
theorem evaluations (r : RatFunc K) (hr : ¬ ∃ c : K, r = RatFunc.C c) (k : ℕ) (A : K) :
    let x := algebraMap (RatFunc K) L r
    let D := (x ^ Fintype.card K - x) ^ 2
    (sumNumerator (Fintype.card K) k (algebraMap K L A)).eval x / D =
      algebraMap (RatFunc K) L (substitute r hr (sumCoordinate k A)) ∧
    (numerator (Fintype.card K) k (algebraMap K L A)).eval x / D =
      algebraMap (RatFunc K) L (substitute r hr (coordinate K k A)) := by
  let e := (Algebra.ofId (RatFunc K) L).restrictScalars K
  let q := Fintype.card K
  have hPoly (f : Polynomial K) :
      (f.map (algebraMap K L)).eval (e r) / ((e r) ^ q - e r) ^ 2 =
      e (substitute r hr (algebraMap K[X] (RatFunc K) f /
        ((RatFunc.X : RatFunc K) ^ q - RatFunc.X) ^ 2)) := by
    rw [substitute_ratio, map_div₀, map_pow, map_sub, map_pow, eval_map_algebraMap,
      aeval_algHom_apply]
  have hN : (numerator q k A).map (algebraMap K L) = numerator q k (algebraMap K L A) := by
    simp [numerator, map_ofNat]
  have hS : (sumNumerator q k A).map (algebraMap K L) = sumNumerator q k (algebraMap K L A) := by
    simp [sumNumerator, hN, map_ofNat]
  constructor
  · have he := hPoly (sumNumerator q k A)
    rw [hS] at he
    exact he
  · have he := hPoly (numerator q k A)
    rw [hN] at he
    rw [diffCoordinate_eq]
    exact he

end

end ManuscriptAudit.CubicFrobeniusCoordinateEvaluation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusCoordinateEvaluation.diffCoordinate_eq,
      ``ManuscriptAudit.CubicFrobeniusCoordinateEvaluation.power_ne_of_nonconstant,
      ``ManuscriptAudit.CubicFrobeniusCoordinateEvaluation.evaluations] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
