import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.GaloisField
import PrimalitySheafVerification.ManuscriptAudit.CubicOddExtensionTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicSquareExtensionTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5ExtensionRecurrence

/-! Actual even- and odd-degree extension traces at primes congruent to two modulo three. -/

namespace ManuscriptAudit.Paper5NonsplitExtensionRecurrence

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open CubicHasseBound CubicJacobiBound CubicJacobiRoots CubicJacobiExtension
open CubicGeometricTorsion CubicCharacterMultiplicity
open CubicSquareExtensionTrace CubicOddExtensionTrace Paper5ExtensionRecurrence
open DavenportHasseJacobi LanglandsFirstMainLemma FiniteFieldPointCount
open Paper5PrintedRecurrence

noncomputable section

variable {p : ℕ} [Fact p.Prime]
  {D : Type*} [Field D] [Fintype D] [DecidableEq D] [Algebra (ZMod p) D]

private theorem base_no_cubicCharacter (hp3 : p % 3 = 2) :
    ¬ 3 ∣ Fintype.card (ZMod p) - 1 := by
  rw [ZMod.card, Nat.dvd_iff_mod_eq_zero]
  have hp := (Fact.out : p.Prime).pos
  omega

private theorem jacobiRoot_degree_two_scalar
    (hF : ringChar (ZMod p) ≠ 2) (hD : ringChar D ≠ 2)
    (hp3 : p % 3 = 2) (hdegree : Module.finrank (ZMod p) D = 2)
    {χ : MulChar D ℂ} (hχ : orderOf χ = 3)
    {A : ZMod p} (hA : A ≠ 0) :
    jacobiRoot χ (algebraMap (ZMod p) D A) = jacobiRoot χ (1 : D) := by
  have hξ (b : ZMod p) (hb : b ≠ 0) : χ (algebraMap (ZMod p) D b) = 1 := by
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective (cube_injective (base_no_cubicCharacter hp3)) b
    have hb' : algebraMap (ZMod p) D b ≠ 0 := by
      simpa only [map_zero] using (algebraMap (ZMod p) D).injective.ne hb
    exact (cube_iff_character_one hχ hb').mp
      ⟨algebraMap (ZMod p) D x, by rw [← map_pow, hx]⟩
  have hχA : χ (-algebraMap (ZMod p) D A) = 1 := by
    rw [← map_neg]
    exact hξ (-A) (neg_ne_zero.mpr hA)
  have hχ1 : χ (-1 : D) = 1 := by
    simpa only [map_neg, map_one] using hξ (-1) (neg_ne_zero.mpr one_ne_zero)
  have hφ : quadraticComplex (algebraMap (ZMod p) D A) = 1 := by
    rw [← norm_quadraticComplex hF hD, norm_character_algebraMap, hdegree,
      ← MulChar.pow_apply' (quadraticComplex : MulChar (ZMod p) ℂ) (by decide : (2 : ℕ) ≠ 0),
      quadraticComplex_sq, MulChar.one_apply hA.isUnit]
  simp only [jacobiRoot, hχA, hχ1, hφ, map_one, one_mul]

variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

private theorem even_extension_trace (hp : 5 ≤ p) (hp3 : p % 3 = 2)
    {k : ℕ} (hd : Module.finrank (ZMod p) E = 2 * k)
    {A : ZMod p} (hA : A ≠ 0) :
    (Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) =
      2 * (-(p : ℤ)) ^ k := by
  classical
  let D := GaloisField p 2
  letI : Fintype D := Fintype.ofFinite D
  have hD : Module.finrank (ZMod p) D = 2 := GaloisField.finrank p (n := 2) (by decide)
  have hcard : Fintype.card D = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by decide)
  have hdd : Module.finrank (ZMod p) D ∣ Module.finrank (ZMod p) E := by
    rw [hD, hd]
    exact dvd_mul_right _ _
  obtain ⟨f⟩ : Nonempty (D →ₐ[ZMod p] E) := FiniteField.nonempty_algHom_of_finrank_dvd hdd
  algebraize [f.toRingHom]
  have hDE : Module.finrank D E = k := by
    have h := Module.finrank_mul_finrank (ZMod p) D E
    rw [hD, hd] at h
    omega
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ringChar.eq (ZMod p) p]; omega
  have hDC : ringChar D ≠ 2 := by rw [ringChar.eq D p]; omega
  have hE : ringChar E ≠ 2 := by rw [ringChar.eq E p]; omega
  have hp2 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)
  have hq3 : Fintype.card D % 3 = 1 := by
    have hh : p ≡ 2 [MOD 3] := by simpa [Nat.ModEq] using hp3
    rw [hcard]
    simpa [Nat.ModEq] using hh.pow 2
  have hdiv : 3 ∣ Fintype.card D - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hpos : 0 < Fintype.card D := Fintype.card_pos
    omega
  obtain ⟨χ, hχ⟩ := exists_orderThree_character (F := D) hdiv
  obtain ⟨ψ, hψ⟩ := primeField_additiveCharacter (p := p)
  have hψD := (traceAddChar_ne_one_iff (ZMod p) D ψ).mpr hψ
  have hΔD : (shortCubic (0 : D) 1).Δ ≠ 0 := by
    simpa only [map_one] using reducedK_good (E := D) hp (A := 1) one_ne_zero
  have hroot := square_extension_jacobiRoot hp3 hp2 hDC hcard hΔD hχ
  have hroot' := (jacobiRoots_eq_at_one hp3 hp2 hDC hχ).symm.trans hroot
  let B := algebraMap (ZMod p) D A
  have hB : B ≠ 0 := by
    simpa only [B, map_zero] using (algebraMap (ZMod p) D).injective.ne hA
  have hα : jacobiRoot χ B = -(p : ℂ) :=
    (jacobiRoot_degree_two_scalar hF hDC hp3 hD hχ hA).trans hroot
  have hβ : jacobiRoot (χ ^ 2) B = -(p : ℂ) :=
    (jacobiRoot_degree_two_scalar hF hDC hp3 hD (orderThree_sq hχ) hA).trans hroot'
  have hAmap : algebraMap D E B = algebraMap (ZMod p) E A :=
    (IsScalarTower.algebraMap_apply (ZMod p) D E A).symm
  have hΔE : (shortCubic (0 : E) (algebraMap D E B)).Δ ≠ 0 := by
    rw [hAmap]
    exact reducedK_good hp hA
  have ht := extension_actual_point_count hDC hE hχ hψD hB hΔE
  rw [hAmap, ← printed_cubic_baseChange_eq_zero p A, hDE, hα, hβ, ← two_mul] at ht
  exact_mod_cast ht

theorem zero_recurrence_at_even (p k : ℕ) :
    recurrence p 0 (2 * k) = 2 * (-(p : ℤ)) ^ k := by
  induction k with
  | zero => norm_num [recurrence]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, recurrence, zero_mul, zero_sub, ih, pow_succ]
    ring

theorem zero_recurrence_at_odd (p k : ℕ) :
    recurrence p 0 (2 * k + 1) = 0 := by
  induction k with
  | zero => norm_num [recurrence]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, recurrence, zero_mul, ih]
    ring

theorem actual_extension_trace_eq_recurrence_of_mod_two (hp : 5 ≤ p) (hp3 : p % 3 = 2)
    {A : ZMod p} (hA : A ≠ 0) :
    (Fintype.card E : ℤ) + 1 -
      (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) =
      recurrence p ((p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ))
        (Module.finrank (ZMod p) E) := by
  let n := Module.finrank (ZMod p) E
  rw [PrimalitySheafVerification.ManuscriptAudit.paper5_traceCurve_trace_eq_zero hp hp3 hA]
  change _ = recurrence p 0 n
  by_cases ht : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, zero_recurrence_at_even]
    exact even_extension_trace hp hp3 hn hA
  · letI : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
    have hE : ringChar E ≠ 2 := by rw [ringChar.eq E p]; omega
    have hn : n = 2 * (n / 2) + 1 := by omega
    have ho : Odd n := ⟨n / 2, hn⟩
    have hc := odd_extension_projective_count hp3 ho hE (reducedK_good (E := E) hp hA)
    rw [← printed_cubic_baseChange_eq_zero p A] at hc
    rw [hn, zero_recurrence_at_odd, hc]
    push_cast
    ring

end
end ManuscriptAudit.Paper5NonsplitExtensionRecurrence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5NonsplitExtensionRecurrence.zero_recurrence_at_even,
      ``ManuscriptAudit.Paper5NonsplitExtensionRecurrence.zero_recurrence_at_odd,
      ``ManuscriptAudit.Paper5NonsplitExtensionRecurrence.actual_extension_trace_eq_recurrence_of_mod_two] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
