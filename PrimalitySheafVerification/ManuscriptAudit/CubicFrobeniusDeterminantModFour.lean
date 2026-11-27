import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitFrobeniusModFourDeterminant
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.PowerTateCoefficientReduction

/-! The actual centered Frobenius determinant modulo four over every good finite field. -/

namespace ManuscriptAudit.CubicFrobeniusDeterminantModFour

open CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius CubicDoublingSurjective
open CubicThreeFrobeniusSigns PowerTateModule PowerTateCoefficientReduction

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L]
  [IsAlgClosed L] [DecidableEq L]

private theorem card_mod_three_ne_zero (h₃ : (3 : E) ≠ 0) : Fintype.card E % 3 ≠ 0 := by
  have hchar : ringChar E ≠ 3 := by
    intro he
    exact h₃ ((ringChar.spec E 3).mpr (by simpa only [he] using (dvd_rfl : (3 : ℕ) ∣ 3)))
  obtain ⟨n, hp, hq⟩ := FiniteField.card E (ringChar E)
  intro hz
  have hd := Nat.dvd_iff_mod_eq_zero.mpr hz
  rw [hq] at hd
  exact hchar ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow hd)).symm

private theorem adic_reduction {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) :
    PadicInt.toZModPow 2 (LinearMap.det (endMap 2 (arithmeticPointFrobenius E L A))) =
      LinearMap.det (levelFrobenius E L A 2) := by
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  have hAL : algebraMap E L A ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  let G := GeometricPoints E L A
  let B := CubicTwoPowerTorsionBasis.affineBasis h₂L h₃L hAL 1
  have hDiv : Function.Surjective (fun P : G => (2 : ℕ) • P) :=
    affine_doubling_surjective h₂L h₃L hAL
  exact (trace_det_reduce 2 G B hDiv (arithmeticPointFrobenius E L A) 2).2

/-- The determinant of the actual arithmetic Frobenius on four-torsion equals the size of any
finite base field of characteristic different from two and three, in Z/4. -/
theorem determinant_eq_card {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    LinearMap.det (levelFrobenius E L A 2) = (Fintype.card E : ZMod 4) := by
  by_cases hq : Fintype.card E % 3 = 2
  · have hAdic : LinearMap.det (endMap 2 (arithmeticPointFrobenius E L A)) =
        (Fintype.card E : ℤ_[2]) :=
      CubicNonsplitTwoThreeAdicCharpoly.two_adic_determinant E L h₂ h₃ hA hq
    rw [← adic_reduction E L h₂ h₃ hA, hAdic, map_natCast]
  · have h0 := card_mod_three_ne_zero E h₃
    have h1 : Fintype.card E % 3 = 1 := by omega
    obtain ⟨z, hz⟩ := finite_exists_primitive_cube_root h1
    exact CubicSplitFrobeniusModFourDeterminant.native_determinant_eq_card E L h₂ h₃ hA hz

/-- The same residue is the determinant of arithmetic Frobenius on the geometric two-adic Tate module. -/
theorem adic_determinant_mod_four {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    PadicInt.toZModPow 2 (LinearMap.det (endMap 2 (arithmeticPointFrobenius E L A))) =
      (Fintype.card E : ZMod 4) :=
  (adic_reduction E L h₂ h₃ hA).trans (determinant_eq_card E L h₂ h₃ hA)

end
end ManuscriptAudit.CubicFrobeniusDeterminantModFour

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusDeterminantModFour.determinant_eq_card,
      ``ManuscriptAudit.CubicFrobeniusDeterminantModFour.adic_determinant_mod_four] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
