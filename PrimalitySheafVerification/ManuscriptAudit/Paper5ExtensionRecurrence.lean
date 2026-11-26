import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiExtension
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts

/-! Actual higher extension traces of the split-cubic-character reductions. -/

namespace ManuscriptAudit.Paper5ExtensionRecurrence

open PrimalitySheafVerification.ManuscriptAudit
  (paper5TraceCurve paper5_traceCurve_discriminant_ne_zero)
open Paper5PrintedRecurrence
open CubicJacobiRoots CubicJacobiExtension CubicGeometricTorsion
open FiniteFieldPointCount CubicCharacterMultiplicity

noncomputable section

theorem recurrence_cast_eq_root_powers (p : ℕ) (a : ℤ) (α β : ℂ)
    (hs : α + β = (a : ℂ)) (hm : α * β = (p : ℂ)) (n : ℕ) :
    (recurrence p a n : ℂ) = α ^ n + β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [recurrence]
  | one => simpa only [recurrence, pow_one] using hs.symm
  | more n hn hn' =>
    rw [recurrence, Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast, hn, hn',
      ← hs, ← hm]
    simp only [pow_succ]
    ring

variable {p : ℕ} [Fact p.Prime]
  {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

private theorem reducedK_good (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    (shortCubic (0 : E) (algebraMap (ZMod p) E A)).Δ ≠ 0 := by
  rw [← printed_cubic_baseChange_eq_zero p A, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
  intro h
  apply paper5_traceCurve_discriminant_ne_zero hp hA
  apply (algebraMap (ZMod p) E).injective
  simpa only [map_zero] using h

theorem actual_extension_trace_eq_recurrence (hp : 5 ≤ p) (hp3 : p % 3 = 1)
    {A : ZMod p} (hA : A ≠ 0) :
    ((Fintype.card E : ℤ) + 1 -
      (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ)) =
      recurrence p ((p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ))
        (Module.finrank (ZMod p) E) := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    omega
  letI : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
  have hE : ringChar E ≠ 2 := by
    rw [ringChar.eq E p]
    omega
  have hdiv : 3 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card, Nat.dvd_iff_mod_eq_zero]
    omega
  obtain ⟨χ, hχ⟩ := exists_orderThree_character (F := ZMod p) hdiv
  obtain ⟨ψ, hψ⟩ := DavenportHasseJacobi.primeField_additiveCharacter (p := p)
  have he : shortCubic (0 : ZMod p) A = paper5TraceCurve p A := by
    ext <;> simp [shortCubic, paper5TraceCurve]
  have hΔ : (shortCubic (0 : ZMod p) A).Δ ≠ 0 := by
    rw [he]
    exact paper5_traceCurve_discriminant_ne_zero hp hA
  have hs := (projective_count_trace_complex hF hΔ).trans
    (cubicTraceSum_eq_neg_jacobiRoots hF hχ hA)
  rw [ZMod.card, he] at hs
  have hm := jacobiRoots_product hF hχ hA
  rw [ZMod.card] at hm
  let a : ℤ := (p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ)
  have hsum : jacobiRoot χ A + jacobiRoot (χ ^ 2) A = (a : ℂ) := by
    dsimp [a]
    push_cast
    exact hs.symm
  have hrec := recurrence_cast_eq_root_powers p a _ _ hsum hm (Module.finrank (ZMod p) E)
  have hcount := extension_actual_point_count (E := E) hF hE hχ hψ hA (reducedK_good hp hA)
  rw [← printed_cubic_baseChange_eq_zero p A, ← hrec] at hcount
  exact_mod_cast hcount

end
end ManuscriptAudit.Paper5ExtensionRecurrence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5ExtensionRecurrence.recurrence_cast_eq_root_powers,
      ``ManuscriptAudit.Paper5ExtensionRecurrence.actual_extension_trace_eq_recurrence] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
