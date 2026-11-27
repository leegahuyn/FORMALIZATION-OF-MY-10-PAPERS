import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Finite.Basic
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferencePolynomial
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceDerivative
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceCancellation

/-! Local multiplicities in the common factor of the actual subtraction formula. -/

namespace ManuscriptAudit.CubicFrobeniusDifferenceGCD

open Polynomial CubicFrobeniusDifferenceNumerator CubicFrobeniusDifferencePolynomial
open CubicFrobeniusDifferenceDerivative CubicFrobeniusDifferenceCancellation

noncomputable section

variable (K : Type*) [Field K] [Fintype K]

/-- The actual subtraction denominator. -/
def denominator : K[X] := (X ^ Fintype.card K - X) ^ 2

theorem denominator_ne_zero : denominator K ≠ 0 :=
  pow_ne_zero _ (FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card)

theorem denominator_multiplicity (x : K) : (denominator K).rootMultiplicity x = 2 := by
  classical
  let D : K[X] := X ^ Fintype.card K - X
  have hD : D ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have hRoots : D.roots = (Finset.univ : Finset K).val := FiniteField.roots_X_pow_card_sub_X K
  have hc : D.roots.count x = 1 := by
    rw [hRoots]
    exact Multiset.count_eq_one_of_mem Finset.univ.nodup (by simp)
  change (D ^ 2).rootMultiplicity x = 2
  rw [← count_roots, pow_two, roots_mul (mul_ne_zero hD hD), Multiset.count_add, hc]

theorem gcd_multiplicity {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : K) :
    (gcd f g).rootMultiplicity x = min (f.rootMultiplicity x) (g.rootMultiplicity x) := by
  have hfg : gcd f g ≠ 0 := by
    intro h
    have hd : (0 : K[X]) ∣ f := by simpa only [h] using (gcd_dvd_left f g)
    exact hf (zero_dvd_iff.mp hd)
  apply le_antisymm
  · exact le_min (rootMultiplicity_le_rootMultiplicity_of_dvd hf (gcd_dvd_left f g) x)
      (rootMultiplicity_le_rootMultiplicity_of_dvd hg (gcd_dvd_right f g) x)
  · rw [le_rootMultiplicity_iff hfg]
    exact dvd_gcd ((le_rootMultiplicity_iff hf).mp (min_le_left _ _))
      ((le_rootMultiplicity_iff hg).mp (min_le_right _ _))

/-- Every cancelled factor has exactly the multiplicity dictated by its ordinate. -/
theorem cancellation_multiplicity {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (hk : 0 < k) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hchar : ringChar K ≠ 2) {A : K} (hA : A ≠ 0) (x : K) :
    (gcd (numerator (Fintype.card K) k A) (denominator K)).rootMultiplicity x =
      cancellation K k A x := by
  classical
  let N := numerator (Fintype.card K) k A
  let s := x ^ 3 + A
  have hN : N ≠ 0 := by
    intro he
    have hdeg := numerator_natDegree hq hk A
    change N.natDegree = 2 * Fintype.card K + 1 at hdeg
    rw [he, natDegree_zero] at hdeg
    omega
  rw [gcd_multiplicity K hN (denominator_ne_zero K), denominator_multiplicity K]
  change min (N.rootMultiplicity x) 2 = if s = 0 then 1 else if s ^ k = -1 then 2 else 0
  by_cases hs : s = 0
  · have hr := zero_ordinate_simple K hq hk h₃ hA hs
    have hLow : 0 < N.rootMultiplicity x := (rootMultiplicity_pos hN).mpr hr.1
    have hHigh : N.rootMultiplicity x ≤ 1 := by
      apply (rootMultiplicity_le_iff hN x 1).mpr
      exact fun hd => hr.2 (square_linear_dvd_iff.mp hd).2
    simp only [hs, if_true]
    omega
  · by_cases hn : s ^ k = -1
    · have hr := nonsquare_root K hq hn
      have hb : 2 ≤ N.rootMultiplicity x :=
        (le_rootMultiplicity_iff hN).mpr (square_linear_dvd_iff.mpr hr)
      simp [hs, hn, min_eq_right hb]
    · have hk' : Fintype.card K / 2 = k := by omega
      have hOne : s ^ k = 1 := by
        have h := FiniteField.pow_dichotomy hchar hs
        rw [hk'] at h
        exact h.resolve_right hn
      have hr : ¬ N.IsRoot x := by
        change N.eval x ≠ 0
        change (numerator (Fintype.card K) k A).eval x ≠ 0
        rw [eval_rational K A x, show x ^ 3 + A = s by rfl, hOne, one_add_one_eq_two]
        exact mul_ne_zero (mul_ne_zero h₂ hs) h₂
      simp [hs, hn, rootMultiplicity_eq_zero hr]

end

end ManuscriptAudit.CubicFrobeniusDifferenceGCD

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusDifferenceGCD.denominator_ne_zero,
      ``ManuscriptAudit.CubicFrobeniusDifferenceGCD.denominator_multiplicity,
      ``ManuscriptAudit.CubicFrobeniusDifferenceGCD.gcd_multiplicity,
      ``ManuscriptAudit.CubicFrobeniusDifferenceGCD.cancellation_multiplicity] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
