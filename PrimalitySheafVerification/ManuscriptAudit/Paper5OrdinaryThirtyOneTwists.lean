import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticTwistCoefficientFormula
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticResidueClass
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOneTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTatePointCounts

/-! Every nonzero characteristic-thirty-one twist has the exact native Tate point-count polynomial. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtyOneTwists

open Polynomial Module FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicFrobeniusSexticTwists CubicOrdinatePreservingTwist CubicSexticTwistCoefficientFormula
open CubicSplitExtensionTraceRecurrence Paper5PrintedPointCounts Paper5OrdinaryThirtyOneCoordinates
open PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

private def representative : Fin 6 → ℕ := ![1, 3, 5, 7, 11, 15]

/-- The twist's signed trace as a function of its sextic residue. -/
def prediction (A : ZMod 31) : ℤ :=
  predictedTrace (5 : ZMod 31) (A ^ 5) 1 6

private theorem representatives_cover : ∀ A : ZMod 31, A ≠ 0 →
    ∃ j : Fin 6, (representative j : ZMod 31) ≠ 0 ∧
      A ^ 5 = (representative j : ZMod 31) ^ 5 := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem representatives_checked : ∀ j : Fin 6,
    (32 : ℤ) - (enumeratedPointsFor 31 (representative j) : ℤ) =
      prediction (representative j : ZMod 31) := by decide

private theorem paper_curve_eq (A : ZMod 31) :
    paper5TraceCurve 31 A = shortCubic (0 : ZMod 31) A := by
  simp [paper5TraceCurve, shortCubic, show (31 : ZMod 31) = 0 by decide]

private theorem representative_trace (j : Fin 6) (h : (representative j : ZMod 31) ≠ 0) :
    signedTrace (representative j : ZMod 31) = prediction (representative j : ZMod 31) := by
  have hc := projective_count_eq_enumeratedFor (p := 31) (A := representative j) (by decide) h
  rw [paper_curve_eq] at hc
  unfold signedTrace
  rw [hc, ZMod.card]
  exact representatives_checked j

/-- The six kernel-checked representatives give the arithmetic trace for every nonzero twist. -/
theorem prediction_eq_count {A : ZMod 31} (hA : A ≠ 0) :
    prediction A = signedTrace A := by
  obtain ⟨j, hR, hPow⟩ := representatives_cover A hA
  have hEq := CubicSexticResidueClass.signedTrace_eq_of_residue (k := 5)
    (by decide) (by rw [ZMod.card]) (by decide) (by decide) hA hR hPow
  unfold prediction
  rw [hPow]
  exact (representative_trace j hR).symm.trans hEq.symm

variable (L : Type*) [Field L] [Algebra (ZMod 31) L] [CharP L 31] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

private theorem primitive_five : IsPrimitiveRoot (5 : ZMod 31) 3 :=
  IsPrimitiveRoot.iff_orderOf.mpr ((orderOf_eq_prime_iff (p := 3)).mpr ⟨by decide, by decide⟩)

abbrev action (A : ZMod 31) : Module.End ℤ_[l] (Tate l (Geometric (ZMod 31) L A)) :=
  endMap l (arithmeticFrobenius (ZMod 31) L A)

def basis (hl : l = 2 ∨ l = 3) {A : ZMod 31} (hA : A ≠ 0) :
    Basis (Fin 2) ℤ_[l] (Tate l (Geometric (ZMod 31) L A)) :=
  CubicRotationTateRankTwo.tateBasis (A := algebraMap (ZMod 31) L A) (z := (5 : L))
    (numeral_ne_zero L 2 (by decide)) (numeral_ne_zero L 3 (by decide))
    ((map_ne_zero (algebraMap (ZMod 31) L)).mpr hA) (cube_rotation L) (rotation_ne_one L) l hl

/-- The Frobenius trace and determinant agree with the actual arithmetic coefficients for every twist. -/
theorem trace_det (hl : l = 2 ∨ l = 3) {A : ZMod 31} (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 31) L A)) (action L l A) =
      (signedTrace A : ℤ_[l]) ∧ LinearMap.det (action L l A) = 31 := by
  have h₂ := numeral_ne_zero L 2 (by decide)
  have h₃ := numeral_ne_zero L 3 (by decide)
  have hF := Paper5OrdinaryThirtyOneFrobenius.native_eq_rotation L
  have h := CubicSexticTwistCoefficientFormula.trace_det (A := (1 : ZMod 31)) (B := A)
    (k := 5) h₂ h₃ one_ne_zero hA (by rw [ZMod.card]) primitive_five 1 6
    (by simpa only [map_ofNat, one_zsmul, ofNat_zsmul] using hF) l hl
  obtain ⟨ht, hd⟩ := h
  change LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 31) L A)) (action L l A) =
    (predictedTrace (5 : ZMod 31) ((A / 1) ^ 5) 1 6 : ℤ_[l]) at ht
  rw [div_one] at ht
  change _ = (prediction A : ℤ_[l]) at ht
  rw [prediction_eq_count hA] at ht
  exact ⟨ht, by simpa only [show (1 : ℤ) ^ 2 - 1 * 6 + 6 ^ 2 = 31 by decide,
    Int.cast_ofNat] using hd⟩

/-- Actual geometric Tate characteristic polynomial for all nonzero F31 twists. -/
theorem charpoly_eq_count (hl : l = 2 ∨ l = 3) {A : ZMod 31} (hA : A ≠ 0) :
    letI := Module.Free.of_basis (basis L l hl hA)
    letI := Module.Finite.of_basis (basis L l hl hA)
    (action L l A).charpoly = X ^ 2 - C (signedTrace A : ℤ_[l]) * X + C (31 : ℤ_[l]) := by
  let B := basis L l hl hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det L l hl hA
  change (action L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l A) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

/-- Every finite-extension projective count agrees with the actual Frobenius power trace. -/
theorem trace_eq_extension_count (E : Type*) [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod 31) E] (hl : l = 2 ∨ l = 3) {A : ZMod 31} (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 31) L A))
      (action L l A ^ Module.finrank (ZMod 31) E) =
    (((Fintype.card E : ℤ) + 1 -
      (Nat.card ((paper5TraceCurve 31 A).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det L l hl hA
  apply Paper5SplitTatePointCounts.trace_power_eq_extension_count (p := 31) (E := E)
    (by decide) (by decide) hA (basis L l hl hA) (action L l A)
  · simpa only [signedTrace, ZMod.card, paper_curve_eq] using ht
  · simpa only [Nat.cast_ofNat] using hd

end
end ManuscriptAudit.Paper5OrdinaryThirtyOneTwists

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTwists.prediction_eq_count,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTwists.trace_det,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTwists.charpoly_eq_count,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTwists.trace_eq_extension_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
