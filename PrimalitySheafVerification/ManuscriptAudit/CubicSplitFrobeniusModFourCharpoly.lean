import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitFrobeniusModFourTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitModFourFullTwoTorsion
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence

/-! Native rank-two characteristic polynomials modulo four in the arithmetic trace cases. -/

namespace ManuscriptAudit.CubicSplitFrobeniusModFourCharpoly

open Polynomial Module CubicThreeTorsionOrdinate TorsionFrobeniusModule
open CubicSplitTwoPowerFrobenius CubicSplitFrobeniusModFourPatterns
open CubicSplitExtensionTraceRecurrence Paper5PrintedRecurrence

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [Algebra K L] [DecidableEq L]

private theorem arithmetic_trace {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3)
    (h : (Fintype.card K : ZMod 4) = 1 ∨ Nat.card (Torsion 2 (Curve A).Point) = 4) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      (signedTrace A : ZMod 4) := by
  rcases h with hq | hRat
  · exact CubicSplitFrobeniusModFourTrace.native_trace_eq_count K L h₂ h₃ hA hz hq
  · simpa only [signedTrace, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one] using
      CubicSplitModFourFullTwoTorsion.trace_eq_signed_count K L h₂ h₃ hA hz hRat

private def rotationBasis {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) : Basis (Fin 2) (ZMod 4) (Level K L A 2) :=
  (exists_native_rotation_form K L h₂ h₃ hA hz).choose

/-- The actual characteristic polynomial over Z/4 has the finite-field coefficients whenever
the field size is one modulo four or the rational two-torsion is full. -/
theorem charpoly_eq_signed_count {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3)
    (h : (Fintype.card K : ZMod 4) = 1 ∨ Nat.card (Torsion 2 (Curve A).Point) = 4) :
    let B := rotationBasis K L h₂ h₃ hA hz
    letI : Module.Free (ZMod 4) (Level K L A 2) := Module.Free.of_basis B
    letI : Module.Finite (ZMod 4) (Level K L A 2) := Module.Finite.of_basis B
    (levelFrobenius K L A 2).charpoly =
      X ^ 2 - C (signedTrace A : ZMod 4) * X + C (Fintype.card K : ZMod 4) := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  let F := levelFrobenius K L A 2
  let B := rotationBasis K L h₂ h₃ hA hz
  letI : Module.Free (ZMod 4) (Level K L A 2) := Module.Free.of_basis B
  letI : Module.Finite (ZMod 4) (Level K L A 2) := Module.Finite.of_basis B
  have ht : LinearMap.trace (ZMod 4) (Level K L A 2) F = (signedTrace A : ZMod 4) :=
    arithmetic_trace K L h₂ h₃ hA hz h
  have hd : LinearMap.det F = (Fintype.card K : ZMod 4) :=
    CubicSplitFrobeniusModFourDeterminant.native_determinant_eq_card K L h₂ h₃ hA hz
  change F.charpoly = _
  rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 4) B, LinearMap.det_toMatrix B, ht, hd]

/-- The exact arithmetic coefficient comparison controls every power of the native map
on geometric four-torsion. -/
theorem trace_power_eq_recurrence {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3)
    (h : (Fintype.card K : ZMod 4) = 1 ∨ Nat.card (Torsion 2 (Curve A).Point) = 4)
    (n : ℕ) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2 ^ n) =
      (recurrence (Fintype.card K) (signedTrace A) n : ZMod 4) := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  obtain ⟨B, _, _, _, _, _⟩ := exists_native_rotation_form K L h₂ h₃ hA hz
  exact Paper5LinearTraceRecurrence.trace_pow_eq_recurrence B (levelFrobenius K L A 2)
    (Fintype.card K) (signedTrace A) (arithmetic_trace K L h₂ h₃ hA hz h)
    (CubicSplitFrobeniusModFourDeterminant.native_determinant_eq_card K L h₂ h₃ hA hz) n

end
end ManuscriptAudit.CubicSplitFrobeniusModFourCharpoly

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSplitFrobeniusModFourCharpoly.charpoly_eq_signed_count,
      ``ManuscriptAudit.CubicSplitFrobeniusModFourCharpoly.trace_power_eq_recurrence] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
