import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Perfect
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.LinearCombination

/-! Paper 4's two torus counts and the direction of their uniqueness. -/

namespace ManuscriptAudit.TorusFrobeniusCounts

variable (K : Type*) [Field K]

abbrev Nonzero := {x : K // x ≠ 0}

abbrev positiveSolutions (p A : ℕ) :=
  {xy : Nonzero K × Nonzero K // xy.1.val ^ p + xy.2.val ^ A = 0}

abbrev negativeSolutions (p A : ℕ) :=
  {xy : Nonzero K × Nonzero K // xy.1.val ^ (-(p : ℤ)) + xy.2.val ^ A = 0}

private def invertNonzero : Nonzero K ≃ Nonzero K where
  toFun x := ⟨x.val⁻¹, inv_ne_zero x.property⟩
  invFun x := ⟨x.val⁻¹, inv_ne_zero x.property⟩
  left_inv x := Subtype.ext (inv_inv x.val)
  right_inv x := Subtype.ext (inv_inv x.val)

private abbrev graphValues (A : ℕ) (e : Nonzero K ≃ Nonzero K) :=
  {xy : Nonzero K × Nonzero K // (e xy.1).val + xy.2.val ^ A = 0}

private def target (A : ℕ) (y : Nonzero K) : Nonzero K :=
  ⟨-(y.val ^ A), neg_ne_zero.mpr (pow_ne_zero A y.property)⟩

private def graphEquiv (A : ℕ) (e : Nonzero K ≃ Nonzero K) :
    Nonzero K ≃ graphValues K A e where
  toFun y := ⟨(e.symm (target K A y), y), by
    rw [e.apply_symm_apply]
    exact neg_add_cancel _⟩
  invFun z := z.val.2
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      change -(z.val.2.val ^ A) = (e z.val.1).val
      linear_combination -z.property
    · rfl

noncomputable section

variable [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

private def frobeniusPermutation : Nonzero K ≃ Nonzero K where
  toFun x := ⟨frobeniusEquiv K p x.val,
    (map_ne_zero_iff (frobeniusEquiv K p) (frobeniusEquiv K p).injective).mpr x.property⟩
  invFun x := ⟨(frobeniusEquiv K p).symm x.val,
    (map_ne_zero_iff (frobeniusEquiv K p).symm (frobeniusEquiv K p).symm.injective).mpr x.property⟩
  left_inv x := Subtype.ext ((frobeniusEquiv K p).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((frobeniusEquiv K p).apply_symm_apply x.val)

def positiveEquiv (A : ℕ) : Nonzero K ≃ positiveSolutions K p A :=
  graphEquiv K A (frobeniusPermutation K p)

def negativeEquiv (A : ℕ) : Nonzero K ≃ negativeSolutions K p A :=
  (graphEquiv K A ((invertNonzero K).trans (frobeniusPermutation K p))).trans
    (Equiv.subtypeEquivProp (funext fun xy => propext (by
      change xy.1.val⁻¹ ^ p + xy.2.val ^ A = 0 ↔ xy.1.val ^ (-(p : ℤ)) + xy.2.val ^ A = 0
      rw [zpow_neg, zpow_natCast, inv_pow])))

/-- Both printed signs give one solution for each nonzero second coordinate. -/
theorem unit_solution_counts (A : ℕ) :
    Nat.card (positiveSolutions K p A) + 1 = Nat.card K ∧
    Nat.card (negativeSolutions K p A) + 1 = Nat.card K := by
  classical
  letI : Fintype (Nonzero K) := Fintype.ofFinite _
  letI : Fintype K := Fintype.ofFinite _
  have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : K))
  rw [Fintype.card_option] at h
  have ht : Nat.card (Nonzero K) + 1 = Nat.card K := by
    simpa only [Nat.card_eq_fintype_card] using h
  exact ⟨by rw [← Nat.card_congr (positiveEquiv K p A), ht],
    by rw [← Nat.card_congr (negativeEquiv K p A), ht]⟩

theorem prime_power_counts (n A : ℕ) (hn : n ≠ 0) :
    Nat.card (positiveSolutions (GaloisField p n) p A) = p ^ n - 1 ∧
    Nat.card (negativeSolutions (GaloisField p n) p A) = p ^ n - 1 := by
  have h := unit_solution_counts (GaloisField p n) p A
  rw [GaloisField.card p (n := n) hn] at h
  omega

end

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The manuscript's asserted uniqueness for a fixed first coordinate fails for both signs. -/
theorem five_two_distinct_second_coordinates :
    (1 : ZMod 5) ≠ 4 ∧
      ((4 : ZMod 5) ^ (5 : ℕ) + 1 ^ (2 : ℕ) = 0) ∧
      ((4 : ZMod 5) ^ (5 : ℕ) + 4 ^ (2 : ℕ) = 0) ∧
      ((4 : ZMod 5) ^ (-5 : ℤ) + 1 ^ (2 : ℕ) = 0) ∧
      ((4 : ZMod 5) ^ (-5 : ℤ) + 4 ^ (2 : ℕ) = 0) := by
  have hpos : (4 : ZMod 5) ^ (5 : ℕ) = 4 := by decide
  have hs : (4 : ZMod 5) * 4 = 1 := by decide
  have hinv : (4 : ZMod 5)⁻¹ = 4 := by
    calc
      _ = (4 : ZMod 5)⁻¹ * 1 := (mul_one _).symm
      _ = (4 : ZMod 5)⁻¹ * (4 * 4) := by rw [hs]
      _ = 4 := by rw [← mul_assoc, inv_mul_cancel₀ (by decide : (4 : ZMod 5) ≠ 0), one_mul]
  have hneg : (4 : ZMod 5) ^ (-5 : ℤ) = 4 := by
    rw [show (-5 : ℤ) = -(5 : ℤ) by decide, zpow_neg]
    change ((4 : ZMod 5) ^ (5 : ℕ))⁻¹ = 4
    rw [hpos, hinv]
  rw [hneg]
  decide

end ManuscriptAudit.TorusFrobeniusCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.TorusFrobeniusCounts.positiveEquiv,
      ``ManuscriptAudit.TorusFrobeniusCounts.negativeEquiv,
      ``ManuscriptAudit.TorusFrobeniusCounts.unit_solution_counts,
      ``ManuscriptAudit.TorusFrobeniusCounts.prime_power_counts,
      ``ManuscriptAudit.TorusFrobeniusCounts.five_two_distinct_second_coordinates] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
