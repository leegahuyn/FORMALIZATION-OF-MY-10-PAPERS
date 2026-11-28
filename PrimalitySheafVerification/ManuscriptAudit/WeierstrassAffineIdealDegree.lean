import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineDedekind
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassIdealDegree

/-! Degree of actual nonzero geometric affine Weierstrass ideals. Each
prime factor contributes its quotient dimension, namely one. -/

namespace ManuscriptAudit.WeierstrassAffineIdealDegree

open WeierstrassCurve.Affine FractionalIdeal UniqueFactorizationMonoid
open scoped nonZeroDivisors

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

local instance : IsDedekindDomain W.CoordinateRing :=
  WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W

/-- Geometric affine degree is the dimension of the actual quotient ring. -/
def degree (I : Ideal W.CoordinateRing) : ℕ :=
  Module.finrank K (W.CoordinateRing ⧸ I)

private theorem ideal_invertible (I : Ideal W.CoordinateRing) (hI : I ≠ 0) :
    Module.Invertible W.CoordinateRing I := by
  let A := W.CoordinateRing
  let F := W.FunctionField
  let U := FractionalIdeal.unitsMulEquivSubmodule
    (FractionalIdeal.mk0 F (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ : (Ideal A)⁰))
  let e : I ≃ₗ[A] (U : Submodule A F) :=
    Submodule.equivMapOfInjective (Algebra.linearMap A F) (IsFractionRing.injective A F) I
  exact Module.Invertible.congr e.symm

/-- A nonzero prime ideal adds one to the degree of a nonzero integral ideal. -/
theorem degree_prime_mul {P I : Ideal W.CoordinateRing} (hP : Prime P) (hI : I ≠ 0) :
    degree W (P * I) = degree W I + 1 := by
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  letI : Module.Invertible W.CoordinateRing I := ideal_invertible W I hI
  letI : Module.Finite K (W.CoordinateRing ⧸ (P * I)) :=
    WeierstrassIdealDegree.nonzero_quotient_finite W _ (mul_ne_zero hP.ne_zero hI)
  exact WeierstrassIdealDegree.quotient_degree_mul_rational I P
    (WeierstrassAffineClosedPoints.residueEquiv W P).symm

private theorem degree_prod (s : Multiset (Ideal W.CoordinateRing))
    (hs : ∀ P ∈ s, Prime P) : degree W s.prod = s.card := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, Multiset.card_zero, Ideal.one_eq_top]
    change Module.finrank K (W.CoordinateRing ⧸ (⊤ : Ideal W.CoordinateRing)) = 0
    exact Module.finrank_zero_of_subsingleton
  | cons P s ih =>
    have hP := hs P (Multiset.mem_cons_self P s)
    have ht (Q : Ideal W.CoordinateRing) (hQ : Q ∈ s) : Prime Q :=
      hs Q (Multiset.mem_cons_of_mem hQ)
    rw [Multiset.prod_cons, Multiset.card_cons,
      degree_prime_mul W hP (Multiset.prod_ne_zero fun h => (ht 0 h).ne_zero rfl), ih ht]

/-- Every affine quotient degree is the number of prime factors, with multiplicity. -/
theorem degree_eq_card_factors (I : Ideal W.CoordinateRing) (hI : I ≠ 0) :
    degree W I = (normalizedFactors I).card := by
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  exact degree_prod W (normalizedFactors I) fun P hP => prime_of_normalized_factor P hP

/-- Quotient degree is additive on products of nonzero integral ideals. -/
theorem degree_mul {I J : Ideal W.CoordinateRing} (hI : I ≠ 0) (hJ : J ≠ 0) :
    degree W (I * J) = degree W I + degree W J := by
  rw [degree_eq_card_factors W _ (mul_ne_zero hI hJ), degree_eq_card_factors W _ hI,
    degree_eq_card_factors W _ hJ, normalizedFactors_mul hI hJ, Multiset.card_add]

end

end ManuscriptAudit.WeierstrassAffineIdealDegree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassAffineIdealDegree.degree_prime_mul,
      ``ManuscriptAudit.WeierstrassAffineIdealDegree.degree_eq_card_factors,
      ``ManuscriptAudit.WeierstrassAffineIdealDegree.degree_mul] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
