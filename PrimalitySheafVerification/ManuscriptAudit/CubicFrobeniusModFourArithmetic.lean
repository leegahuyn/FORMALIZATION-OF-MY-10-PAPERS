import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDeterminantModFour
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitFrobeniusModFourTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitModFourFullTwoTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitCubeTwoTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitNoncubeModFourTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusCharpoly
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence

/-! Native mod-four Frobenius coefficients over every good finite field for the centered cubic. -/

namespace ManuscriptAudit.CubicFrobeniusModFourArithmetic

open Polynomial Module FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicNonsplitFrobeniusTrace CubicSplitTwoPowerFrobenius
open CubicSplitExtensionTraceRecurrence CubicThreeFrobeniusSigns CubicThreePointCounts
open TorsionFrobeniusModule Paper5PrintedRecurrence

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [Algebra K L] [DecidableEq L]

private theorem nonsplit_trace {A : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (h : Fintype.card K % 3 = 2) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      (signedTrace A : ZMod 4) := by
  let W := Curve A
  let V := Curve (algebraMap K L A)
  let he := centered_baseChange K L A
  let e := torsionTransport L 4 he
  let g := FiniteField.frobeniusAlgHom K L
  let F := pointMap 4 W g
  have hTransport : e.conj F = levelFrobenius K L A 2 :=
    mapLinear_transport K L W V he g 4
  have hTrace : LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) = 0 :=
    (congrArg (LinearMap.trace (ZMod 4) (Level K L A 2)) hTransport.symm).trans
      ((LinearMap.trace_conj' F e).trans (actual_trace_zero K L h₂ h₃ hA h 2))
  rw [hTrace, signedTrace, projective_count_residue_two A h₂ h₃ hA h]
  simp [Nat.cast_add]

/-- On geometric four-torsion, the native trace is the signed projective point count. -/
theorem trace_eq_signed_count {A : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      (signedTrace A : ZMod 4) := by
  by_cases hns : Fintype.card K % 3 = 2
  · exact nonsplit_trace K L h₂ h₃ hA hns
  · have hn := CubicThreeFrobeniusCharpoly.field_card_mod_three_ne_zero K h₃
    have hq3 : Fintype.card K % 3 = 1 := by omega
    obtain ⟨z, hz⟩ := finite_exists_primitive_cube_root hq3
    by_cases hq4 : (Fintype.card K : ZMod 4) = 1
    · exact CubicSplitFrobeniusModFourTrace.native_trace_eq_count K L h₂ h₃ hA hz hq4
    · by_cases hcube : ∃ u : K, u ^ 3 = A
      · have ht := CubicSplitCubeTwoTorsion.rationalTwoTorsion_card h₂ h₃ hA hz hcube
        simpa only [signedTrace, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one] using
          CubicSplitModFourFullTwoTorsion.trace_eq_signed_count K L h₂ h₃ hA hz ht
      · have hchar : ringChar K ≠ 2 := by
          intro he
          exact h₂ ((ringChar.spec K 2).mpr (by simpa only [he] using (dvd_rfl : (2 : ℕ) ∣ 2)))
        have hOdd := FiniteField.odd_card_of_char_ne_two hchar
        have hne : Fintype.card K % 4 ≠ 1 := fun h =>
          hq4 ((ZMod.natCast_eq_natCast_iff' (Fintype.card K) 1 4).mpr h)
        have hq4' : (Fintype.card K : ZMod 4) = 3 :=
          (ZMod.natCast_eq_natCast_iff' (Fintype.card K) 3 4).mpr (by omega)
        exact CubicSplitNoncubeModFourTrace.native_trace_eq_count K L h₂ h₃ hA hz hcube hq4'

private def basisOfGoodCentered {A : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Basis (Fin 2) (ZMod 4) (Level K L A 2) := by
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L A ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  exact CubicTwoPowerTorsionBasis.affineBasis h₂L h₃L hAL 2

/-- The characteristic polynomial of actual arithmetic Frobenius on geometric
four-torsion has the exact arithmetic coefficients modulo four. -/
theorem charpoly_eq_signed_count {A : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    let B := basisOfGoodCentered K L h₂ h₃ hA
    letI : Module.Free (ZMod 4) (Level K L A 2) := Module.Free.of_basis B
    letI : Module.Finite (ZMod 4) (Level K L A 2) := Module.Finite.of_basis B
    (levelFrobenius K L A 2).charpoly =
      X ^ 2 - C (signedTrace A : ZMod 4) * X + C (Fintype.card K : ZMod 4) := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  let B := basisOfGoodCentered K L h₂ h₃ hA
  letI : Module.Free (ZMod 4) (Level K L A 2) := Module.Free.of_basis B
  letI : Module.Finite (ZMod 4) (Level K L A 2) := Module.Finite.of_basis B
  let F := levelFrobenius K L A 2
  have ht : LinearMap.trace (ZMod 4) (Level K L A 2) F = (signedTrace A : ZMod 4) :=
    trace_eq_signed_count K L h₂ h₃ hA
  have hd : LinearMap.det F = (Fintype.card K : ZMod 4) :=
    CubicFrobeniusDeterminantModFour.determinant_eq_card K L h₂ h₃ hA
  change F.charpoly = _
  rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 4) B, LinearMap.det_toMatrix B, ht, hd]

/-- On actual four-torsion all Frobenius power traces satisfy the point-count recurrence. -/
theorem trace_power_eq_recurrence {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (n : ℕ) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2 ^ n) =
      (recurrence (Fintype.card K) (signedTrace A) n : ZMod 4) := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  exact Paper5LinearTraceRecurrence.trace_pow_eq_recurrence (basisOfGoodCentered K L h₂ h₃ hA)
    (levelFrobenius K L A 2) (Fintype.card K) (signedTrace A) (trace_eq_signed_count K L h₂ h₃ hA)
    (CubicFrobeniusDeterminantModFour.determinant_eq_card K L h₂ h₃ hA) n

end
end ManuscriptAudit.CubicFrobeniusModFourArithmetic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusModFourArithmetic.trace_eq_signed_count,
      ``ManuscriptAudit.CubicFrobeniusModFourArithmetic.charpoly_eq_signed_count,
      ``ManuscriptAudit.CubicFrobeniusModFourArithmetic.trace_power_eq_recurrence] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
