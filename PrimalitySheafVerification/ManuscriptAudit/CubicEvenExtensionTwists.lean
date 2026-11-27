import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiExtension

/-! A nonsplit centered twist becomes the unit twist in every even-degree extension. -/

namespace ManuscriptAudit.CubicEvenExtensionTwists

open CubicJacobiRoots CubicJacobiExtension CubicJacobiBound DavenportHasseJacobi
open LanglandsFirstMainLemma

noncomputable section

variable (F E : Type*) [Field F] [Fintype F] [DecidableEq F]
variable [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

theorem square_in_even_extension (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2)
    (hEven : Even (Module.finrank F E)) (a : F) : IsSquare (algebraMap F E a) := by
  by_cases ha : a = 0
  · simp [ha]
  have haE : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ha
  have hNorm := congrArg (fun χ : MulChar E ℂ => χ (algebraMap F E a))
    (norm_quadraticComplex hF hE)
  rw [norm_character_algebraMap] at hNorm
  obtain ⟨n, hn⟩ := hEven
  have hn' : Module.finrank F E = 2 * n := by omega
  have hSquare : ((quadraticComplex : MulChar F ℂ) a) ^ (2 : ℕ) = 1 := by
    change ((quadraticChar F a : ℤ) : ℂ) ^ (2 : ℕ) = 1
    exact_mod_cast quadraticChar_sq_one ha
  rw [hn', pow_mul, hSquare, one_pow] at hNorm
  apply (quadraticChar_one_iff_isSquare haE).mp
  change (1 : ℂ) = ((quadraticChar E (algebraMap F E a) : ℤ) : ℂ) at hNorm
  exact_mod_cast hNorm.symm

theorem nonzero_cube_root (hQ : Fintype.card F % 3 = 2) {a : F} (ha : a ≠ 0) :
    ∃ b : F, b ≠ 0 ∧ b ^ (3 : ℕ) = a := by
  let m := Fintype.card F - 1
  let k := (2 * m + 1) / 3
  have hk : k * 3 = 2 * m + 1 := by
    dsimp [k, m]
    omega
  refine ⟨a ^ k, pow_ne_zero _ ha, ?_⟩
  rw [← pow_mul, hk, pow_add, show 2 * m = m * 2 by omega, pow_mul]
  have hFermat : a ^ m = 1 := FiniteField.pow_card_sub_one_eq_one a ha
  rw [hFermat]
  simp

theorem sixth_root_in_even_extension (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2)
    (hQ : Fintype.card F % 3 = 2) (hEven : Even (Module.finrank F E))
    {a : F} (ha : a ≠ 0) :
    ∃ u : E, u ≠ 0 ∧ u ^ (6 : ℕ) = algebraMap F E a := by
  obtain ⟨b, hb, hb₃⟩ := nonzero_cube_root F hQ ha
  obtain ⟨u, hu⟩ := square_in_even_extension F E hF hE hEven b
  have hu₂ : u ^ (2 : ℕ) = algebraMap F E b := by
    simpa only [pow_two] using hu.symm
  have hU : u ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hu₂
    exact (map_ne_zero (algebraMap F E)).mpr hb hu₂.symm
  refine ⟨u, hU, ?_⟩
  calc
    u ^ (6 : ℕ) = (u ^ (2 : ℕ)) ^ (3 : ℕ) := by rw [← pow_mul]
    _ = algebraMap F E a := by rw [hu₂, ← map_pow, hb₃]

end
end ManuscriptAudit.CubicEvenExtensionTwists

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicEvenExtensionTwists.square_in_even_extension,
      ``ManuscriptAudit.CubicEvenExtensionTwists.nonzero_cube_root,
      ``ManuscriptAudit.CubicEvenExtensionTwists.sixth_root_in_even_extension] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
