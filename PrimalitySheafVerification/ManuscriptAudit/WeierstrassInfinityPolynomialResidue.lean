import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityPoleCoordinates

/-! Polynomial functions in the original x-coordinate have their exact
pole orders determined by the leading coefficient at the Cartier origin. -/

namespace ManuscriptAudit.WeierstrassInfinityPolynomialResidue

open Polynomial
open scoped BigOperators
open WeierstrassInfinityChartAlgebra WeierstrassInfinityOriginIdeal
open WeierstrassInfinityOpenCover WeierstrassInfinityPoleCoordinates

noncomputable section

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev N := Neighborhood W
private abbrev P := Puncture W

def localBracket : N W :=
  algebraMap (WeierstrassInfinityChartAlgebra.Ring W) (N W) (bracket W)

theorem localOrigin_bracket : localOrigin W (localBracket W) = 1 :=
  (localOrigin_map W _).trans (origin_bracket W)

/-- This regular expression clears the proposed pole of a polynomial in x. -/
def scaledPolynomial (p : K[X]) (d : ℕ) : N W :=
  ∑ i ∈ p.support, algebraMap K (N W) (p.coeff i) * localBracket W ^ i *
    localX W ^ (d - 2 * i)

private theorem scaledPower (i d : ℕ) (h : 2 * i ≤ d) :
    xAffine W ^ i * punctureX W ^ d =
      punctureBracket W ^ i * punctureX W ^ (d - 2 * i) := by
  calc
    _ = xAffine W ^ i * (punctureX W ^ (2 * i) * punctureX W ^ (d - 2 * i)) := by
      rw [← pow_add, Nat.add_sub_of_le h]
    _ = (xAffine W * punctureX W ^ 2) ^ i * punctureX W ^ (d - 2 * i) := by
      rw [mul_pow, ← pow_mul, mul_assoc]
    _ = _ := by rw [x_pole_equation]

theorem scaledPolynomial_on_puncture (p : K[X]) (d : ℕ) (hd : 2 * p.natDegree ≤ d) :
    algebraMap (N W) (P W) (scaledPolynomial W p d) =
      p.eval₂ (algebraMap K (P W)) (xAffine W) * punctureX W ^ d := by
  rw [scaledPolynomial, Polynomial.eval₂_eq_sum, Polynomial.sum_def, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  change algebraMap K (P W) (p.coeff i) * punctureBracket W ^ i *
      punctureX W ^ (d - 2 * i) =
    (algebraMap K (P W) (p.coeff i) * xAffine W ^ i) * punctureX W ^ d
  rw [mul_assoc, mul_assoc (algebraMap K (P W) (p.coeff i)), scaledPower W i d
    ((Nat.mul_le_mul_left 2 (Polynomial.le_natDegree_of_mem_supp hi)).trans hd)]

private theorem term_residue (p : K[X]) (d i : ℕ) (hdi : 2 * i ≤ d) :
    localOrigin W (algebraMap K (N W) (p.coeff i) * localBracket W ^ i *
        localX W ^ (d - 2 * i)) = if d = 2 * i then p.coeff i else 0 := by
  have hc : localOrigin W (algebraMap K (N W) (p.coeff i)) = p.coeff i :=
    (localOrigin W).commutes (p.coeff i)
  rw [map_mul, map_mul, map_pow, map_pow, hc, localOrigin_bracket, localOrigin_x, one_pow, mul_one]
  by_cases h : d = 2 * i
  · rw [h, Nat.sub_self, if_pos rfl, pow_zero, mul_one]
  · have hn : d - 2 * i ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hdi (Ne.symm h))
    rw [if_neg h, zero_pow hn, mul_zero]

/-- After clearing a strictly larger denominator, the residue is zero. -/
theorem residue_of_larger_pole (p : K[X]) (d : ℕ) (hd : 2 * p.natDegree < d) :
    localOrigin W (scaledPolynomial W p d) = 0 := by
  rw [scaledPolynomial, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have h : 2 * i < d :=
    (Nat.mul_le_mul_left 2 (Polynomial.le_natDegree_of_mem_supp hi)).trans_lt hd
  rw [term_residue W p d i h.le, if_neg h.ne']

/-- At the exact cleared pole the residue is the polynomial's leading coefficient. -/
theorem residue_at_exact_pole (p : K[X]) :
    localOrigin W (scaledPolynomial W p (2 * p.natDegree)) = p.leadingCoeff := by
  classical
  by_cases hp : p = 0
  · simp [hp, scaledPolynomial]
  rw [scaledPolynomial, map_sum]
  rw [Finset.sum_eq_single p.natDegree]
  · rw [term_residue W p _ _ le_rfl, if_pos rfl] <;> rfl
  · intro i hi hne
    have h : 2 * i < 2 * p.natDegree := Nat.mul_lt_mul_of_pos_left
      (lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp hi) hne) (by decide)
    rw [term_residue W p _ _ h.le, if_neg h.ne']
  · intro h
    exact (h (Polynomial.natDegree_mem_support_of_nonzero hp)).elim

end

end ManuscriptAudit.WeierstrassInfinityPolynomialResidue

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityPolynomialResidue.scaledPolynomial_on_puncture,
      ``ManuscriptAudit.WeierstrassInfinityPolynomialResidue.residue_of_larger_pole,
      ``ManuscriptAudit.WeierstrassInfinityPolynomialResidue.residue_at_exact_pole] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
