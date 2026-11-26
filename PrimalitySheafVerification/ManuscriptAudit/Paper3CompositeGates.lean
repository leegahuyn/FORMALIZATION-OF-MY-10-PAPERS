import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum

/-!
# Composite inputs pass the four explicit predicates of Paper 3

Physical pp. 60–62 describe an Archimedean window, a normalized modular
divisor, a p-adic valuation bound, and the discriminant of the
Weierstrass curve. At p = 3, A = 23, k = 1, M = 2, both exponents 3
and 6 give composite inputs passing all four conditions. These two
exponents cover the indexed-prime and product readings at n = 2.
The EC predicate here is the stated discriminant condition.
-/

namespace ManuscriptAudit.Paper3CompositeGates

open WeierstrassCurve

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def testCurve : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 1⟩

theorem discriminant_good :
    (testCurve.map (Int.castRingHom (ZMod 3))).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  have h : (testCurve.map (Int.castRingHom (ZMod 3))).Δ = 1 := by decide
  rw [h]
  exact isUnit_one

/-- The four explicit local predicates and their coprime overlap. -/
def passes (r : ℕ) (c : ℝ) : Prop :=
  let Y := 23 ^ r
  let X := Y + 3
  (23 : ℝ) ^ (-c * (r : ℝ)) ≤ |(X : ℝ) - (Y : ℝ)| ∧
  |(X : ℝ) - (Y : ℝ)| ≤ 23 / (r : ℝ) ∧
  (∃ y : ℤ, (2 : ℤ) = (r : ℤ) * y - (23 - 1)) ∧
  2 ∣ X ∧
  padicValNat 3 Y + 1 ≤ padicValNat 3 (X - Y) ∧
  (testCurve.map (Int.castRingHom (ZMod 3))).IsElliptic ∧
  Nat.Coprime 2 3

private theorem lower_bound (c : ℝ) (hc : 1 < c) (r : ℕ) (hr : 0 < r) :
    (23 : ℝ) ^ (-c * (r : ℝ)) ≤ 3 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hc' : 0 < c := lt_trans zero_lt_one hc
  have hs : -c * (r : ℝ) < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hc') hr'
  exact (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hs).le.trans (by norm_num)

private theorem composite_of_even (X : ℕ) (hX : 2 < X) (hd : 2 ∣ X) :
    ¬ Nat.Prime X := by
  intro hp
  rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega

/-- The second indexed prime gives exponent three and composite input 12170. -/
theorem indexed_prime_composite_passes (c : ℝ) (hc : 1 < c) :
    passes 3 c ∧ ¬ Nat.Prime (23 ^ 3 + 3) := by
  refine ⟨?_, composite_of_even _ (by decide) (by decide)⟩
  have hv : padicValNat 3 (23 ^ 3) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide)
  have he : |((23 ^ 3 + 3 : ℕ) : ℝ) - ((23 ^ 3 : ℕ) : ℝ)| = 3 := by norm_num
  change (23 : ℝ) ^ (-c * (3 : ℝ)) ≤ _ ∧ _ ≤ 23 / (3 : ℝ) ∧
    (∃ y : ℤ, (2 : ℤ) = 3 * y - (23 - 1)) ∧
    2 ∣ 23 ^ 3 + 3 ∧
    padicValNat 3 (23 ^ 3) + 1 ≤ padicValNat 3 ((23 ^ 3 + 3) - 23 ^ 3) ∧
    _ ∧ _
  rw [he, hv, show (23 ^ 3 + 3) - 23 ^ 3 = 3 by decide, padicValNat_self]
  exact ⟨lower_bound c hc 3 (by decide), by norm_num, ⟨8, by norm_num⟩,
    by decide, le_rfl, discriminant_good, by decide⟩

/-- Multiplying p by n gives exponent six and another composite input. -/
theorem product_exponent_composite_passes (c : ℝ) (hc : 1 < c) :
    passes 6 c ∧ ¬ Nat.Prime (23 ^ 6 + 3) := by
  refine ⟨?_, composite_of_even _ (by decide) (by decide)⟩
  have hv : padicValNat 3 (23 ^ 6) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide)
  have he : |((23 ^ 6 + 3 : ℕ) : ℝ) - ((23 ^ 6 : ℕ) : ℝ)| = 3 := by norm_num
  change (23 : ℝ) ^ (-c * (6 : ℝ)) ≤ _ ∧ _ ≤ 23 / (6 : ℝ) ∧
    (∃ y : ℤ, (2 : ℤ) = 6 * y - (23 - 1)) ∧
    2 ∣ 23 ^ 6 + 3 ∧
    padicValNat 3 (23 ^ 6) + 1 ≤ padicValNat 3 ((23 ^ 6 + 3) - 23 ^ 6) ∧
    _ ∧ _
  rw [he, hv, show (23 ^ 6 + 3) - 23 ^ 6 = 3 by decide, padicValNat_self]
  exact ⟨lower_bound c hc 6 (by decide), by norm_num, ⟨4, by norm_num⟩,
    by decide, le_rfl, discriminant_good, by decide⟩

end

end ManuscriptAudit.Paper3CompositeGates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper3CompositeGates.discriminant_good,
      ``ManuscriptAudit.Paper3CompositeGates.indexed_prime_composite_passes,
      ``ManuscriptAudit.Paper3CompositeGates.product_exponent_composite_passes] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
