import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiRoots
import PrimalitySheafVerification.ManuscriptAudit.DavenportHasseJacobi

/-! The two Jacobi roots lift by powers over finite-field extensions. -/

namespace ManuscriptAudit.CubicJacobiExtension

open CubicJacobiRoots CubicJacobiBound CubicHasseBound DavenportHasseJacobi
open LanglandsFirstMainLemma FiniteFieldPointCount

noncomputable section

variable {F E : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

private theorem character_sq_one_generator {χ : MulChar E ℂ} (hn : χ ≠ 1)
    (hs : χ ^ 2 = 1) {g : Eˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    χ (g : E) = -1 := by
  have hgen : χ (g : E) ≠ 1 := by
    intro he
    apply hn
    apply MulChar.equivToUnitHom.injective
    change χ.toUnitHom = (1 : MulChar E ℂ).toUnitHom
    apply (MonoidHom.eq_iff_eq_on_generator hg _ _).mpr
    apply Units.ext
    change χ (g : E) = (1 : MulChar E ℂ) (g : E)
    rw [MulChar.one_apply_coe, he]
  have hsq : χ (g : E) ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, hs, MulChar.one_apply_coe]
  have hf : (χ (g : E) - 1) * (χ (g : E) + 1) = 0 := by
    linear_combination hsq
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hgen))

theorem norm_quadraticComplex (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2) :
    normMulChar F E (quadraticComplex : MulChar F ℂ) = quadraticComplex := by
  let χ : MulChar E ℂ := normMulChar F E (quadraticComplex : MulChar F ℂ)
  have hn : χ ≠ 1 := (normMulChar_ne_one_iff F E _).mpr (quadraticComplex_ne_one hF)
  have hs : χ ^ 2 = 1 := by
    change (normCharacter (F := F) (E := E) quadraticComplex) ^ 2 = 1
    rw [← map_pow, quadraticComplex_sq, map_one]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  apply MulChar.equivToUnitHom.injective
  change χ.toUnitHom = (quadraticComplex : MulChar E ℂ).toUnitHom
  apply (MonoidHom.eq_iff_eq_on_generator hg _ _).mpr
  apply Units.ext
  change χ (g : E) = (quadraticComplex : MulChar E ℂ) (g : E)
  rw [character_sq_one_generator hn hs hg,
    character_sq_one_generator (quadraticComplex_ne_one hE) quadraticComplex_sq hg]

private theorem normCharacter_orderThree {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    orderOf (normCharacter (F := F) (E := E) χ) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply (orderOf_eq_prime_iff (p := 3)).mpr
  have hc : χ ^ (3 : ℕ) = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  refine ⟨by rw [← map_pow, hc, map_one], ?_⟩
  apply (normMulChar_ne_one_iff F E χ).mpr
  simpa only [pow_one] using ne_one_of_orderThree_pow hχ (by decide : ¬ 3 ∣ (1 : ℕ))

private theorem orderThree_sq {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    orderOf (χ ^ (2 : ℕ)) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply (orderOf_eq_prime_iff (p := 3)).mpr
  refine ⟨?_, ne_one_of_orderThree_pow hχ (by decide : ¬ 3 ∣ (2 : ℕ))⟩
  have h : χ ^ (3 : ℕ) = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, h, one_pow]

theorem jacobiRoot_lift (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2)
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (A : F) :
    jacobiRoot (normCharacter (F := F) (E := E) χ) (algebraMap F E A) =
      (jacobiRoot χ A) ^ Module.finrank F E := by
  have hprod : χ * quadraticComplex ≠ 1 := by
    intro he
    exact ne_one_of_orderThree_pow hχ (by decide : ¬ 3 ∣ (2 : ℕ))
      (by rw [mul_quadratic_eq_one he, quadraticComplex_sq])
  have hJ := negative_jacobi_lift (E := E) χ quadraticComplex ψ hψ hprod
  unfold jacobiRoot
  change normMulChar F E χ (-algebraMap F E A) * quadraticComplex (algebraMap F E A) *
      (-jacobiSum (normMulChar F E χ) quadraticComplex) = _
  rw [← norm_quadraticComplex hF hE, ← (algebraMap F E).map_neg A,
    norm_character_algebraMap, norm_character_algebraMap, hJ, ← mul_pow, ← mul_pow]

/-- The trace of genuine projective points over the extension is the sum
of powers of the two base-field Jacobi roots. -/
theorem extension_actual_point_count (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2)
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {A : F} (hA : A ≠ 0) (hΔ : (shortCubic (0 : E) (algebraMap F E A)).Δ ≠ 0) :
    (Fintype.card E : ℂ) + 1 -
        (Nat.card (shortCubic (0 : E) (algebraMap F E A)).toProjective.Point : ℂ) =
      (jacobiRoot χ A) ^ Module.finrank F E + (jacobiRoot (χ ^ 2) A) ^ Module.finrank F E := by
  let ρ : MulChar F ℂ →* MulChar E ℂ := normCharacter
  have hA' : algebraMap F E A ≠ 0 := (algebraMap F E).injective.ne hA
  have hρ : orderOf (ρ χ) = 3 := normCharacter_orderThree hχ
  have hpow : (ρ χ) ^ (2 : ℕ) = ρ (χ ^ (2 : ℕ)) := (map_pow ρ χ 2).symm
  rw [projective_count_trace_complex hE hΔ, cubicTraceSum_eq_neg_jacobiRoots hE hρ hA',
    hpow]
  exact congrArg₂ (· + ·) (jacobiRoot_lift hF hE hχ hψ A)
    (jacobiRoot_lift hF hE (orderThree_sq hχ) hψ A)

end
end ManuscriptAudit.CubicJacobiExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicJacobiExtension.norm_quadraticComplex,
      ``ManuscriptAudit.CubicJacobiExtension.jacobiRoot_lift,
      ``ManuscriptAudit.CubicJacobiExtension.extension_actual_point_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
