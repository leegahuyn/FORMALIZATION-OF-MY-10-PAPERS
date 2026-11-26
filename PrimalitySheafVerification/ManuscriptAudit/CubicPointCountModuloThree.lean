import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCharacterMultiplicity

/-! The actual cubic y² = x³ + 1 has a projective point count divisible by three
whenever the cube roots of unity are in the field and the curve is good. -/

namespace ManuscriptAudit.CubicPointCountModuloThree

open CubicJacobiBound CubicCharacterMultiplicity FiniteFieldPointCount
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem cubeMultiplicity_at_zero : cubeMultiplicity (0 : F) = 1 := by
  letI : Unique {x : F // x ^ 3 = 0} :=
    { default := ⟨0, by simp⟩
      uniq := fun x => Subtype.ext (by
        by_contra h
        exact pow_ne_zero 3 h x.property) }
  simp [cubeMultiplicity]

theorem cubeMultiplicity_nonzero_dvd_three (hdiv : 3 ∣ Fintype.card F - 1)
    {z : F} (hz : z ≠ 0) : 3 ∣ cubeMultiplicity z := by
  by_cases h : ∃ x : F, x ^ 3 = z
  · rw [cubeMultiplicity_eq_three hdiv hz h]
  · letI : IsEmpty {x : F // x ^ 3 = z} := ⟨fun x => h ⟨x.val, x.property⟩⟩
    have he : cubeMultiplicity z = 0 := by simp [cubeMultiplicity]
    rw [he]
    exact dvd_zero _

theorem count_cast_zmod_three_zero (hF : ringChar F ≠ 2)
    (hq : (Fintype.card F : ZMod 3) = 1) (hdiv : 3 ∣ Fintype.card F - 1)
    (hΔ : (shortCubic (0 : F) 1).Δ ≠ 0) :
    (Nat.card (shortCubic (0 : F) 1).toProjective.Point : ZMod 3) = 0 := by
  have hs : (∑ x : F, (quadraticChar F (x ^ 3 + (1 : F)) : ZMod 3)) = 1 := by
    rw [← Fintype.sum_fiberwise' (fun x : F => x ^ 3)
      (fun z : F => (quadraticChar F (z + (1 : F)) : ZMod 3))]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_eq_single (0 : F)]
    · rw [show Fintype.card {x : F // x ^ 3 = 0} = 1 from cubeMultiplicity_at_zero]
      simp
    · intro z _ hz
      have hd := cubeMultiplicity_nonzero_dvd_three hdiv hz
      have h0 := (ZMod.natCast_eq_zero_iff (cubeMultiplicity z) 3).mpr hd
      change (cubeMultiplicity z : ZMod 3) * _ = 0
      rw [h0, zero_mul]
    · simp
  have hc := shortCubic_projective_count_int hF hΔ
  simp only [zero_mul, sub_zero] at hc
  have he := congrArg (fun x : ℤ => (x : ZMod 3)) hc
  push_cast at he
  rw [he, hq, hs] <;> decide

end
end ManuscriptAudit.CubicPointCountModuloThree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicPointCountModuloThree.cubeMultiplicity_at_zero,
      ``ManuscriptAudit.CubicPointCountModuloThree.cubeMultiplicity_nonzero_dvd_three,
      ``ManuscriptAudit.CubicPointCountModuloThree.count_cast_zmod_three_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
