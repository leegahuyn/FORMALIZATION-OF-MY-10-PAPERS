import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityWeightedResidue

/-! The pole order of an actual affine Weierstrass function is its algebra
norm degree. Here exactness is expressed by a nonzero residue after clearing. -/

namespace ManuscriptAudit.WeierstrassInfinityNormPole

open Polynomial Module WeierstrassCurve.Affine
open WeierstrassInfinityChartCoordinates WeierstrassInfinityChartAlgebra
open WeierstrassInfinityOriginIdeal WeierstrassInfinityOpenCover
open WeierstrassInfinityPoleCoordinates WeierstrassInfinityPolynomialResidue
open WeierstrassInfinityWeightedResidue
open scoped Polynomial.Bivariate

noncomputable section

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev N := Neighborhood W
private abbrev P := Puncture W

private theorem map_coefficient (p : K[X]) :
    affineToPuncture W (algebraMap K[X] W.CoordinateRing p) =
      p.eval₂ (algebraMap K (P W)) (xAffine W) := by
  let g := (affineToPuncture W).comp (IsScalarTower.toAlgHom K K[X] W.CoordinateRing)
  have h : g = Polynomial.aeval (xAffine W) := by
    apply Polynomial.algHom_ext
    change affineToPuncture W (affineX W) = (Polynomial.aeval (R := K) (xAffine W)) X
    rw [affineToPuncture_x, Polynomial.aeval_X]
  have h' := congrArg (fun e : K[X] →ₐ[K] P W => e p) h
  exact h'

theorem map_smul_basis (p q : K[X]) :
    affineToPuncture W (p • 1 + q • CoordinateRing.mk W Y) = affineValue W p q := by
  change affineToPuncture W (p • 1 + q • affineY W) = _
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul,
    map_coefficient, map_coefficient, affineToPuncture_y, affineValue]

private theorem even_weight (n : ℕ) : 2 • (n : WithBot ℕ) = ((2 * n : ℕ) : WithBot ℕ) := by
  rw [← WithBot.coe_nsmul, nsmul_eq_mul]

private theorem odd_weight (n : ℕ) : 2 • (n : WithBot ℕ) + 3 = ((2 * n + 3 : ℕ) : WithBot ℕ) := by
  rw [even_weight, show (3 : WithBot ℕ) = ((3 : ℕ) : WithBot ℕ) from rfl, ← WithBot.coe_add]

private theorem norm_natDegree_both (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    (Algebra.norm K[X] (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Y)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [CoordinateRing.degree_norm_smul_basis, Polynomial.degree_eq_natDegree hp,
    Polynomial.degree_eq_natDegree hq, even_weight, odd_weight]
  rcases le_total (2 * p.natDegree) (2 * q.natDegree + 3) with h | h
  · rw [max_eq_right h, max_eq_right (WithBot.coe_le_coe.mpr h)]
  · rw [max_eq_left h, max_eq_left (WithBot.coe_le_coe.mpr h)]

private theorem norm_natDegree_even (p : K[X]) (hp : p ≠ 0) :
    (Algebra.norm K[X] (p • (1 : W.CoordinateRing) + (0 : K[X]) • CoordinateRing.mk W Y)).natDegree =
      2 * p.natDegree := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [CoordinateRing.degree_norm_smul_basis, Polynomial.degree_eq_natDegree hp, even_weight]
  simp

private theorem norm_natDegree_odd (q : K[X]) (hq : q ≠ 0) :
    (Algebra.norm K[X] ((0 : K[X]) • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Y)).natDegree =
      2 * q.natDegree + 3 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [CoordinateRing.degree_norm_smul_basis, Polynomial.degree_eq_natDegree hq, odd_weight]
  simp

/-- At the true puncture, every nonzero original affine function, multiplied by
the parameter to its norm degree, extends across infinity with nonzero residue. -/
theorem exact_pole_degree_norm (f : W.CoordinateRing) (hf : f ≠ 0) :
    ∃ a : N W, localOrigin W a ≠ 0 ∧ algebraMap (N W) (P W) a =
      affineToPuncture W f * punctureX W ^ (Algebra.norm K[X] f).natDegree := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
  rw [map_smul_basis]
  by_cases hq : q = 0
  · subst q
    have hp : p ≠ 0 := by
      intro h
      apply hf
      simp [h]
    rw [norm_natDegree_even W p hp]
    refine ⟨scaledPolynomial W p (2 * p.natDegree), ?_, ?_⟩
    · rw [residue_at_exact_pole]
      exact leadingCoeff_ne_zero.mpr hp
    · rw [scaledPolynomial_on_puncture W p _ le_rfl, affineValue, Polynomial.eval₂_zero,
        zero_mul, add_zero]
  · by_cases hp : p = 0
    · subst p
      rw [norm_natDegree_odd W q hq]
      refine ⟨scaledValue W 0 q (2 * q.natDegree + 3), ?_, ?_⟩
      · rw [odd_leading_residue W 0 q (by simp)]
        exact leadingCoeff_ne_zero.mpr hq
      · exact scaledValue_on_puncture W 0 q _ (by simp) le_rfl
    · rw [norm_natDegree_both W p q hp hq]
      exact exact_weighted_leading_residue W p q hp hq

/-- The exact pole exponent is the dimension of the actual affine quotient.
This counts the affine zero scheme of the same original function with multiplicity. -/
theorem exact_pole_degree_quotient (f : W.CoordinateRing) (hf : f ≠ 0) :
    ∃ a : N W, localOrigin W a ≠ 0 ∧ algebraMap (N W) (P W) a =
      affineToPuncture W f * punctureX W ^
        Module.finrank K (W.CoordinateRing ⧸ Ideal.span ({f} : Set W.CoordinateRing)) := by
  rw [finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) hf]
  exact exact_pole_degree_norm W f hf

end

end ManuscriptAudit.WeierstrassInfinityNormPole

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityNormPole.map_smul_basis,
      ``ManuscriptAudit.WeierstrassInfinityNormPole.exact_pole_degree_norm,
      ``ManuscriptAudit.WeierstrassInfinityNormPole.exact_pole_degree_quotient] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
