import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityPolynomialResidue

/-! The two polynomial parts of an affine Weierstrass function have even
and odd candidate pole orders. Their leading residues cannot cancel. -/

namespace ManuscriptAudit.WeierstrassInfinityWeightedResidue

open Polynomial
open WeierstrassInfinityChartAlgebra WeierstrassInfinityOriginIdeal
open WeierstrassInfinityOpenCover WeierstrassInfinityPoleCoordinates
open WeierstrassInfinityPolynomialResidue

noncomputable section

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev N := Neighborhood W
private abbrev P := Puncture W

def affineValue (p q : K[X]) : P W :=
  p.eval₂ (algebraMap K (P W)) (xAffine W) + q.eval₂ (algebraMap K (P W)) (xAffine W) * yAffine W

/-- Integral expression of u^d(p(x)+q(x)y) on the actual infinity neighborhood. -/
def scaledValue (p q : K[X]) (d : ℕ) : N W :=
  scaledPolynomial W p d + localBracket W * scaledPolynomial W q (d - 3)

theorem scaledValue_on_puncture (p q : K[X]) (d : ℕ)
    (hp : 2 * p.natDegree ≤ d) (hq : 2 * q.natDegree + 3 ≤ d) :
    algebraMap (N W) (P W) (scaledValue W p q d) =
      affineValue W p q * punctureX W ^ d := by
  have h3 : 3 ≤ d := by omega
  have hq' : 2 * q.natDegree ≤ d - 3 := by omega
  rw [scaledValue, map_add, map_mul, scaledPolynomial_on_puncture W p d hp,
    scaledPolynomial_on_puncture W q (d - 3) hq', affineValue, add_mul]
  congr 1
  change punctureBracket W * (q.eval₂ (algebraMap K (P W)) (xAffine W) *
      punctureX W ^ (d - 3)) =
    (q.eval₂ (algebraMap K (P W)) (xAffine W) * yAffine W) * punctureX W ^ d
  rw [← y_pole_equation W]
  rw [show punctureX W ^ d = punctureX W ^ 3 * punctureX W ^ (d - 3) by
    rw [← pow_add, Nat.add_sub_of_le h3]]
  ac_rfl

theorem even_leading_residue (p q : K[X]) (h : 2 * q.natDegree + 3 < 2 * p.natDegree) :
    localOrigin W (scaledValue W p q (2 * p.natDegree)) = p.leadingCoeff := by
  have hq : 2 * q.natDegree < 2 * p.natDegree - 3 := by omega
  rw [scaledValue, map_add, map_mul, localOrigin_bracket, residue_at_exact_pole,
    residue_of_larger_pole W q _ hq, mul_zero, add_zero]

theorem odd_leading_residue (p q : K[X]) (h : 2 * p.natDegree < 2 * q.natDegree + 3) :
    localOrigin W (scaledValue W p q (2 * q.natDegree + 3)) = q.leadingCoeff := by
  rw [scaledValue, map_add, map_mul, localOrigin_bracket,
    residue_of_larger_pole W p _ h, show 2 * q.natDegree + 3 - 3 = 2 * q.natDegree by omega,
    residue_at_exact_pole, one_mul, zero_add]

/-- For two nonzero polynomial parts, the larger pole clears the function
with nonzero residue. The odd and even weighted degrees never coincide. -/
theorem exact_weighted_leading_residue (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    let d := max (2 * p.natDegree) (2 * q.natDegree + 3)
    ∃ a : N W, localOrigin W a ≠ 0 ∧
      algebraMap (N W) (P W) a = affineValue W p q * punctureX W ^ d := by
  dsimp only
  let d := max (2 * p.natDegree) (2 * q.natDegree + 3)
  refine ⟨scaledValue W p q d, ?_, scaledValue_on_puncture W p q d (le_max_left _ _) (le_max_right _ _)⟩
  have hne : 2 * p.natDegree ≠ 2 * q.natDegree + 3 := by omega
  rcases lt_or_gt_of_ne hne with h | h
  · change localOrigin W (scaledValue W p q d) ≠ 0
    rw [d, max_eq_right h.le, odd_leading_residue W p q h]
    exact leadingCoeff_ne_zero.mpr hq
  · change localOrigin W (scaledValue W p q d) ≠ 0
    rw [d, max_eq_left h.le, even_leading_residue W p q h]
    exact leadingCoeff_ne_zero.mpr hp

end

end ManuscriptAudit.WeierstrassInfinityWeightedResidue

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityWeightedResidue.scaledValue_on_puncture,
      ``ManuscriptAudit.WeierstrassInfinityWeightedResidue.even_leading_residue,
      ``ManuscriptAudit.WeierstrassInfinityWeightedResidue.odd_leading_residue,
      ``ManuscriptAudit.WeierstrassInfinityWeightedResidue.exact_weighted_leading_residue] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
