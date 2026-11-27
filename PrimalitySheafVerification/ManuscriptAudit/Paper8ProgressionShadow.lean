import Lean.Util.CollectAxioms
import Mathlib.Logic.Equiv.Fin.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8BilateralKroneckerShadow
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianCharacter
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadowNonzero

/-!
# The p. 334 progression and the p. 338 Kronecker target

The signed coefficient on the full progression 1 + 6ℤ already includes
the sign of the negative half. Its bilateral sum is the p. 338
positive-index shadow. The separately printed p. 332 bilateral character
formulation is twice that sum.
-/

namespace ManuscriptAudit.Paper8ProgressionShadow

open Paper8EulerianCharacter (kronecker_nat_mod6)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8KroneckerShadow
open Paper8BilateralKroneckerShadow (bilateralShadow bilateral_eq_two_unary)

noncomputable section

def index (m : ℤ) : ℤ := 6 * m + 1

def progressionTerm (τ : ℂ) (m : ℤ) : ℂ :=
  (index m : ℂ) * Complex.exp (periodCoefficient * (index m : ℂ) ^ 2 * τ / 24)

def progressionShadow (τ : ℂ) : ℂ := ∑' m : ℤ, progressionTerm τ m

theorem progressionTerm_nat (τ : ℂ) (m : ℕ) :
    progressionTerm τ (m : ℤ) = shadowTerm (m * 6 + 1) (rootParameter τ) := by
  have hMod : (m * 6 + 1) % 6 = 1 := by omega
  have hIndex : index (m : ℤ) = ((m * 6 + 1 : ℕ) : ℤ) := by
    unfold index
    push_cast
    ring
  rw [progressionTerm, hIndex, shadowTerm_root_eq_exponential, coefficient,
    kronecker_nat_mod6, if_pos hMod, Int.cast_one, one_mul, Int.cast_natCast]

theorem progressionTerm_neg_succ (τ : ℂ) (m : ℕ) :
    progressionTerm τ (-((m : ℤ) + 1)) = shadowTerm (m * 6 + 5) (rootParameter τ) := by
  have hMod : (m * 6 + 5) % 6 = 5 := by omega
  have hNotOne : (m * 6 + 5) % 6 ≠ 1 := by omega
  have hIndex : index (-((m : ℤ) + 1)) = -((m * 6 + 5 : ℕ) : ℤ) := by
    unfold index
    push_cast
    ring
  rw [progressionTerm, hIndex, shadowTerm_root_eq_exponential, coefficient,
    kronecker_nat_mod6, if_neg hNotOne, if_pos hMod]
  simp only [Int.cast_neg, Int.cast_one, Int.cast_natCast, neg_one_mul, neg_sq]

theorem progression_absolute_summability {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun m : ℤ => ‖progressionTerm τ m‖) := by
  have hSeries := shadowSeries_absolute_summability (rootParameter_norm_lt_one hτ)
  have hinj (j : ℕ) : Function.Injective (fun n : ℕ => n * 6 + j) := by
    intro a b h
    change a * 6 + j = b * 6 + j at h
    omega
  have hBlock (j : ℕ) : Summable (fun n : ℕ => ‖shadowTerm (n * 6 + j) (rootParameter τ)‖) :=
    hSeries.comp_injective (hinj j)
  have hPos : Summable (fun n : ℕ => ‖progressionTerm τ (n : ℤ)‖) :=
    (hBlock 1).congr fun n => congrArg (fun w : ℂ => ‖w‖) (progressionTerm_nat τ n).symm
  have hNeg : Summable (fun n : ℕ => ‖progressionTerm τ (-((n : ℤ) + 1))‖) :=
    (hBlock 5).congr fun n => congrArg (fun w : ℂ => ‖w‖) (progressionTerm_neg_succ τ n).symm
  exact Summable.of_nat_of_neg_add_one (f := fun m : ℤ => ‖progressionTerm τ m‖) hPos hNeg

private theorem residue_block (τ : ℂ) (k : ℕ) :
    (∑ j : Fin 6, shadowTerm (k * 6 + (j : ℕ)) (rootParameter τ)) =
      progressionTerm τ (k : ℤ) + progressionTerm τ (-((k : ℤ) + 1)) := by
  have hEach (j : Fin 6) :
      shadowTerm (k * 6 + (j : ℕ)) (rootParameter τ) =
        (if j = 1 then progressionTerm τ (k : ℤ) else 0) +
          (if j = 5 then progressionTerm τ (-((k : ℤ) + 1)) else 0) := by
    by_cases h₁ : j = 1
    · subst j
      simpa using (progressionTerm_nat τ k).symm
    by_cases h₅ : j = 5
    · subst j
      simpa using (progressionTerm_neg_succ τ k).symm
    have hj : (j : ℕ) < 6 := j.isLt
    have hVal₁ : (j : ℕ) ≠ 1 := fun h => h₁ (Fin.ext h)
    have hVal₅ : (j : ℕ) ≠ 5 := fun h => h₅ (Fin.ext h)
    have hMod₁ : (k * 6 + (j : ℕ)) % 6 ≠ 1 := by omega
    have hMod₅ : (k * 6 + (j : ℕ)) % 6 ≠ 5 := by omega
    rw [shadowTerm, coefficient, kronecker_nat_mod6, if_neg hMod₁, if_neg hMod₅]
    simp only [Int.cast_zero, zero_mul, h₁, h₅, if_false, zero_add]
  simp_rw [hEach, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem progression_eq_p338_unary {τ : ℂ} (hτ : 0 < τ.im) :
    progressionShadow τ = unaryShadow τ := by
  let e : ℕ ≃ ℕ × Fin 6 := Nat.divModEquiv 6
  let f : ℕ → ℂ := fun n => shadowTerm n (rootParameter τ)
  have hGroup : Summable (fun p : ℕ × Fin 6 => f (e.symm p)) :=
    (shadowSeries_absolute_summability (rootParameter_norm_lt_one hτ)).of_norm.comp_injective
      e.symm.injective
  have hPairs := (progression_absolute_summability hτ).of_norm.hasSum.nat_add_neg_add_one
  calc
    progressionShadow τ = ∑' k : ℕ,
        (progressionTerm τ (k : ℤ) + progressionTerm τ (-((k : ℤ) + 1))) :=
      hPairs.tsum_eq.symm
    _ = ∑' k : ℕ, ∑ j : Fin 6, shadowTerm (k * 6 + (j : ℕ)) (rootParameter τ) :=
      tsum_congr fun k => (residue_block τ k).symm
    _ = ∑' p : ℕ × Fin 6, f (e.symm p) := by
      rw [hGroup.tsum_prod]
      refine tsum_congr fun k => ?_
      rw [tsum_fintype] <;> rfl
    _ = unaryShadow τ := e.symm.tsum_eq f

theorem p332_bilateral_eq_two_progression {τ : ℂ} (hτ : 0 < τ.im) :
    bilateralShadow τ = 2 * progressionShadow τ := by
  rw [bilateral_eq_two_unary hτ, progression_eq_p338_unary hτ]

theorem progression_nonzero_on_upper_half_plane :
    ∃ τ : ℂ, 0 < τ.im ∧ progressionShadow τ ≠ 0 := by
  obtain ⟨τ, hτ, hNonzero⟩ := Paper8KroneckerShadowNonzero.unaryShadow_nonzero_on_upper_half_plane
  exact ⟨τ, hτ, by rwa [progression_eq_p338_unary hτ]⟩

end
end ManuscriptAudit.Paper8ProgressionShadow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ProgressionShadow.progressionTerm_nat,
      ``ManuscriptAudit.Paper8ProgressionShadow.progressionTerm_neg_succ,
      ``ManuscriptAudit.Paper8ProgressionShadow.progression_absolute_summability,
      ``ManuscriptAudit.Paper8ProgressionShadow.progression_eq_p338_unary,
      ``ManuscriptAudit.Paper8ProgressionShadow.p332_bilateral_eq_two_progression,
      ``ManuscriptAudit.Paper8ProgressionShadow.progression_nonzero_on_upper_half_plane] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
