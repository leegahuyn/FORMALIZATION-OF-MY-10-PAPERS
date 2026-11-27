import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericSecantHeight
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericZeroHeight
import PrimalitySheafVerification.ManuscriptAudit.QuadraticHeightRelation

/-! The arithmetic characteristic relation at the actual generic centered cubic point. -/

namespace ManuscriptAudit.CubicGenericCharacteristicRelation

open CubicGenericAntiInvariant CubicGenericPointHeight CubicGenericFrobeniusHeight CubicGenericSecantHeight
open CubicFrobeniusCoordinateEvaluation CubicFrobeniusDifferenceCancellation FiniteFieldPointCount
open RationalSubstitutionDegree RationalIdentityHeight

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [Fintype K] (A : K)

/-- Iterating the actual sum map F+1 squares its generic abscissa degree. -/
theorem generic_sum_square_height {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2) (hA : A ≠ 0) :
    let P := genericAntiPoint A h₂ h₃ hA
    let F := frobenius A
    height A (F (F P + P) + (F P + P)) = height A (F P + P) ^ 2 := by
  let P := genericAntiPoint A h₂ h₃ hA
  let F := frobenius A
  let Q := F P + P
  let r := sumCoordinate k A
  have hRep := generic_sum_xRep A hq h₂ h₃ hA
  change Q.val.xRep = ![algebraMap (RatFunc K) _ r, 1] at hRep
  have hDeg : height A Q = rationalDegree r := height_eq_of_xRep A Q r hRep
  have hP : height A P = 1 := genericPoint_height A h₂ h₃ hA
  have hF : height A (F P) = Fintype.card K := by
    rw [height_frobenius A h₂, hP, mul_one]
  have hMinus := generic_difference_height A hq hk h₂ h₃ hchar hA
  have hPara := height_parallelogram A h₂ h₃ hA (F P) P
  change height A Q + height A (F P - P) =
    2 * height A (F P) + 2 * height A P at hPara
  change height A (F P - P) = Nat.card (shortCubic (0 : K) A).toProjective.Point at hMinus
  rw [hMinus, hP, hF, hDeg] at hPara
  have hCount := count_add_cancellation K hq h₂ h₃ hchar hA
  have hPos : 0 < rationalDegree r := by omega
  have hr := nonconstant_of_degree_pos hPos
  obtain ⟨hRep₂, _⟩ := generic_secant_xRep A hq h₂ h₃ hA Q r hr hRep
  change height A (F Q + Q) = height A Q ^ 2
  rw [height_eq_of_xRep A (F Q + Q) _ hRep₂, rationalDegree_substitute, ← hDeg, pow_two]

/-- At the generic point, the exact arithmetic characteristic relation has zero height. -/
theorem generic_relation_height_zero {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2) (hA : A ≠ 0) :
    let P := genericAntiPoint A h₂ h₃ hA
    let F := frobenius A
    let t : ℤ := (Fintype.card K : ℤ) + 1 - Nat.card (shortCubic (0 : K) A).toProjective.Point
    height A (F (F P) - t • F P + (Fintype.card K : ℤ) • P) = 0 := by
  let P := genericAntiPoint A h₂ h₃ hA
  let F := frobenius A
  let D := quadraticHeight A h₂ h₃ hA
  have hP : D P = 1 := by
    change (height A P : ℤ) = 1
    exact_mod_cast (show height A P = 1 from genericPoint_height A h₂ h₃ hA)
  have hF (X : antiInvariant A) : D (F X) = (Fintype.card K : ℤ) * D X := by
    change (height A (F X) : ℤ) = (Fintype.card K : ℤ) * (height A X : ℤ)
    exact_mod_cast (show height A (F X) = Fintype.card K * height A X from height_frobenius A h₂ X)
  have hSquare : D (F (F P + P) + (F P + P)) = D (F P + P) ^ 2 := by
    change (height A (F (F P + P) + (F P + P)) : ℤ) = (height A (F P + P) : ℤ) ^ 2
    have hs : height A (F (F P + P) + (F P + P)) = height A (F P + P) ^ 2 :=
      generic_sum_square_height A hq hk h₂ h₃ hchar hA
    exact_mod_cast hs
  have hEq := QuadraticHeightRelation.height_characteristic_relation D F P
    (Fintype.card K : ℤ) hP hF hSquare
  have hDiff : D (F P - P) = (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ) := by
    change (height A (F P - P) : ℤ) = (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ)
    have hi : height A (F P - P) = Nat.card (shortCubic (0 : K) A).toProjective.Point :=
      generic_difference_height A hq hk h₂ h₃ hchar hA
    exact_mod_cast hi
  dsimp only at hEq
  rw [hDiff] at hEq
  change (height A _ : ℤ) = 0 at hEq
  exact_mod_cast hEq

/-- The actual polynomial in relative Frobenius is killed by two at the generic point. -/
theorem generic_relation_two_nsmul {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2) (hA : A ≠ 0) :
    let P := genericAntiPoint A h₂ h₃ hA
    let F := frobenius A
    let t : ℤ := (Fintype.card K : ℤ) + 1 - Nat.card (shortCubic (0 : K) A).toProjective.Point
    (2 : ℕ) • (F (F P) - t • F P + (Fintype.card K : ℤ) • P) = 0 :=
  CubicGenericZeroHeight.two_nsmul_eq_zero_of_height_zero A h₂ h₃ hA _
    (generic_relation_height_zero A hq hk h₂ h₃ hchar hA)

end

end ManuscriptAudit.CubicGenericCharacteristicRelation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericCharacteristicRelation.generic_sum_square_height,
      ``ManuscriptAudit.CubicGenericCharacteristicRelation.generic_relation_height_zero,
      ``ManuscriptAudit.CubicGenericCharacteristicRelation.generic_relation_two_nsmul] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
