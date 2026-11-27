import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusActual
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeSquareRootDescent

/-! The actual q-Frobenius characteristic polynomial modulo three on the good centered cubic. -/

namespace ManuscriptAudit.CubicThreeFrobeniusCharpoly

open Polynomial WeierstrassCurve FiniteFieldPointCount
open CubicThreeFrobeniusActual CubicThreePointCounts CubicThreeSquareRootDescent
open CubicThreeFrobeniusSigns

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable (E : Type*) [Field E] [Fintype E] [DecidableEq E]
variable (L : Type*) [Field L] [Algebra E L] [DecidableEq L] [IsAlgClosed L]

theorem field_card_mod_three_ne_zero (h₃ : (3 : E) ≠ 0) : Fintype.card E % 3 ≠ 0 := by
  obtain ⟨p, hChar, n, hPrime, hCard⟩ := FiniteField.card' (K := E)
  letI : CharP E p := hChar
  intro hz
  have hd := Nat.dvd_of_mod_eq_zero hz
  rw [hCard] at hd
  have hp := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hPrime).mp
    (Nat.prime_three.dvd_of_dvd_pow hd)
  apply h₃
  have hdiv : p ∣ 3 := hp ▸ (dvd_rfl : 3 ∣ 3)
  simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero_iff E p 3).mpr hdiv

def signedPointTrace (A : E) : ℤ :=
  (Fintype.card E : ℤ) + 1 - (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ)

/-- The two coefficients of native Frobenius are the actual signed point count and q modulo 3. -/
theorem actualFrobenius_arithmetic_trace_det {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    LinearMap.trace (ZMod 3) (ActualTorsion E L A) (actualFrobenius E L A) =
      (signedPointTrace E A : ZMod 3) ∧
      LinearMap.det (actualFrobenius E L A) = (Fintype.card E : ZMod 3) := by
  have hq := field_card_mod_three_ne_zero E h₃
  obtain ⟨a, s, ha, hs, hDet, hTrace⟩ := actualFrobenius_trace_det E L h₂ h₃ hA hq
  refine ⟨?_, hDet⟩
  unfold signedPointTrace
  by_cases hq₁ : Fintype.card E % 3 = 1
  · have hc := squareRoots_card_of_sign h₂ hA ha hs
    have hv : LinearMap.trace (ZMod 3) (ActualTorsion E L A) (actualFrobenius E L A) =
        1 - (Nat.card (SquareRoots A) : ZMod 3) := by
      rw [hTrace, if_pos hq₁, hc]
      cases s <;> decide
    exact hv.trans (signed_count_residue_one A h₂ h₃ hA hq₁).symm
  · have hq₂ : Fintype.card E % 3 = 2 := by omega
    have hz : (((Fintype.card E : ℤ) + 1 -
        (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ)) : ZMod 3) = 0 := by
      simp [projective_count_residue_two A h₂ h₃ hA hq₂, Nat.cast_add]
    exact (show LinearMap.trace (ZMod 3) (ActualTorsion E L A)
      (actualFrobenius E L A) = 0 by simpa [hq₁] using hTrace).trans hz.symm

/-- Characteristic polynomial of the actual native q-power point map over any finite base field. -/
theorem actualFrobenius_arithmetic_charpoly {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    letI := finiteActualTorsionModule E L h₂ h₃ hA
    (actualFrobenius E L A).charpoly =
      X ^ 2 - C (signedPointTrace E A : ZMod 3) * X + C (Fintype.card E : ZMod 3) := by
  letI := finiteActualTorsionModule E L h₂ h₃ hA
  let B := actualTorsionBasis E L h₂ h₃ hA
  let f := actualFrobenius E L A
  change f.charpoly = _
  have h := actualFrobenius_arithmetic_trace_det E L h₂ h₃ hA
  rw [← LinearMap.charpoly_toMatrix f B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 3) B, LinearMap.det_toMatrix B, h.1, h.2]

end
end ManuscriptAudit.CubicThreeFrobeniusCharpoly

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeFrobeniusCharpoly.field_card_mod_three_ne_zero,
      ``ManuscriptAudit.CubicThreeFrobeniusCharpoly.actualFrobenius_arithmetic_trace_det,
      ``ManuscriptAudit.CubicThreeFrobeniusCharpoly.actualFrobenius_arithmetic_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
