import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.FieldTheory.RatFunc.IntermediateField
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceGCD

/-! The rational abscissa of the Frobenius difference has the actual projective point count as its degree. -/

namespace ManuscriptAudit.CubicFrobeniusDifferenceDegree

open Polynomial CubicFrobeniusDifferenceNumerator CubicFrobeniusDifferencePolynomial
open CubicFrobeniusDifferenceCancellation CubicFrobeniusDifferenceGCD FiniteFieldPointCount
open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K] [Fintype K]

/-- A split polynomial over a finite field has degree equal to its total root multiplicity. -/
theorem natDegree_eq_sum_multiplicity {f : K[X]} (hf : f.Splits) :
    f.natDegree = ∑ x : K, f.rootMultiplicity x := by
  classical
  rw [hf.natDegree_eq_card_roots]
  simpa only [count_roots] using
    (Multiset.sum_count_eq_card (s := (Finset.univ : Finset K))
      (m := f.roots) (by simp)).symm

theorem denominator_splits : (denominator K).Splits := by
  let D : K[X] := X ^ Fintype.card K - X
  have hD : D.Splits := by
    rw [splits_iff_card_roots]
    change (X ^ Fintype.card K - X : K[X]).roots.card =
      (X ^ Fintype.card K - X : K[X]).natDegree
    rw [FiniteField.roots_X_pow_card_sub_X K,
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
    exact Finset.card_univ
  exact hD.pow 2

theorem denominator_natDegree : (denominator K).natDegree = 2 * Fintype.card K := by
  unfold denominator
  rw [natDegree_pow, FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]

theorem gcd_natDegree {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (hk : 0 < k) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hchar : ringChar K ≠ 2) {A : K} (hA : A ≠ 0) :
    (gcd (numerator (Fintype.card K) k A) (denominator K)).natDegree =
      ∑ x : K, cancellation K k A x := by
  have hSplit := (denominator_splits K).of_dvd (denominator_ne_zero K) (gcd_dvd_right
    (numerator (Fintype.card K) k A) (denominator K))
  rw [natDegree_eq_sum_multiplicity K hSplit]
  exact Finset.sum_congr rfl (fun x _ => cancellation_multiplicity K hq hk h₂ h₃ hchar hA x)

/-- The normalized degree of a ratio is the larger original degree minus the gcd degree. -/
theorem max_natDegree_div {f g : Polynomial K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hdeg : g.natDegree ≤ f.natDegree) :
    let r : RatFunc K := algebraMap (Polynomial K) (RatFunc K) f /
      algebraMap (Polynomial K) (RatFunc K) g
    max r.num.natDegree r.denom.natDegree = f.natDegree - (gcd f g).natDegree := by
  let d := gcd f g
  have hd : d ≠ 0 := by
    intro he
    have hz : (0 : Polynomial K) ∣ g := by
      simpa only [← show d = gcd f g from rfl, he] using gcd_dvd_right f g
    exact hg (zero_dvd_iff.mp hz)
  have aux (x : Polynomial K) (hx : x ≠ 0) (hxd : d ∣ x) :
      (x / d).natDegree = x.natDegree - d.natDegree := by
    have hprod := EuclideanDomain.mul_div_cancel' hd hxd
    have hquot : x / d ≠ 0 := by
      intro he
      rw [he, mul_zero] at hprod
      exact hx hprod.symm
    have he := congrArg Polynomial.natDegree hprod
    rw [natDegree_mul hd hquot] at he
    omega
  have hgn : g / d ≠ 0 := by
    intro he
    have hprod := EuclideanDomain.mul_div_cancel' hd (show d ∣ g from gcd_dvd_right f g)
    rw [he, mul_zero] at hprod
    exact hg hprod.symm
  have hc : (g / d).leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hgn)
  dsimp only
  rw [RatFunc.num_div, RatFunc.denom_div f hg]
  change max (C (g / d).leadingCoeff⁻¹ * (f / d)).natDegree
    (C (g / d).leadingCoeff⁻¹ * (g / d)).natDegree = f.natDegree - d.natDegree
  rw [natDegree_C_mul hc, natDegree_C_mul hc, aux f hf (gcd_dvd_left f g),
    aux g hg (gcd_dvd_right f g)]
  exact max_eq_left (Nat.sub_le_sub_right hdeg _)

/-- The rational abscissa of relative Frobenius minus the identity, in the x-line's function field. -/
def coordinate (k : ℕ) (A : K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (numerator (Fintype.card K) k A) /
    algebraMap (Polynomial K) (RatFunc K) (denominator K)

/-- The field extension induced by the actual rational abscissa has degree #E(K). -/
theorem finrank_adjoin_coordinate {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (hk : 0 < k) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hchar : ringChar K ≠ 2) {A : K} (hA : A ≠ 0) :
    Module.finrank (IntermediateField.adjoin K {coordinate K k A}) (RatFunc K) =
      Nat.card (shortCubic (0 : K) A).toProjective.Point := by
  let N := numerator (Fintype.card K) k A
  have hN : N.natDegree = 2 * Fintype.card K + 1 := numerator_natDegree hq hk A
  have hN₀ : N ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hN
    omega
  have hD : (denominator K).natDegree ≤ N.natDegree := by
    rw [denominator_natDegree, hN]
    omega
  rw [RatFunc.finrank_eq_max_natDegree]
  change max (coordinate K k A).num.natDegree (coordinate K k A).denom.natDegree = _
  have h := max_natDegree_div K hN₀ (denominator_ne_zero K) hD
  change max (coordinate K k A).num.natDegree (coordinate K k A).denom.natDegree =
    N.natDegree - (gcd N (denominator K)).natDegree at h
  rw [h, hN, gcd_natDegree K hq hk h₂ h₃ hchar hA]
  have hCount := count_add_cancellation K hq h₂ h₃ hchar hA
  omega

end

end ManuscriptAudit.CubicFrobeniusDifferenceDegree

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusDifferenceDegree.natDegree_eq_sum_multiplicity,
      ``ManuscriptAudit.CubicFrobeniusDifferenceDegree.denominator_splits,
      ``ManuscriptAudit.CubicFrobeniusDifferenceDegree.denominator_natDegree,
      ``ManuscriptAudit.CubicFrobeniusDifferenceDegree.gcd_natDegree,
      ``ManuscriptAudit.CubicFrobeniusDifferenceDegree.max_natDegree_div,
      ``ManuscriptAudit.CubicFrobeniusDifferenceDegree.finrank_adjoin_coordinate] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
