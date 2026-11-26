import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Dimension.Finite
import Lean.Elab.Tactic.Omega

/-!
# Regular differentials on the rational two-chart compactification

Write the parameters on the two affine charts as t and s, with
s = t⁻¹. The overlap compatibility for f(t) dt and g(s) ds is the
Laurent polynomial identity f(t) + t⁻² g(t⁻¹) = 0. The nonnegative
and at-most-negative-two coefficient ranges are disjoint.
-/

namespace ManuscriptAudit.RationalChartGenus

open Polynomial

noncomputable section

variable (K : Type*) [Field K]

private def north : Polynomial K →ₗ[K] LaurentPolynomial K :=
  Polynomial.toLaurentAlg.toLinearMap

private def south : Polynomial K →ₗ[K] LaurentPolynomial K where
  toFun p := LaurentPolynomial.invert (north K p) * LaurentPolynomial.T (-2)
  map_add' p q := by simp [add_mul]
  map_smul' a p := by
    change LaurentPolynomial.invert (north K (a • p)) * LaurentPolynomial.T (-2) =
      a • (LaurentPolynomial.invert (north K p) * LaurentPolynomial.T (-2))
    rw [map_smul, map_smul, smul_mul_assoc]

private def overlap : Polynomial K × Polynomial K →ₗ[K] LaurentPolynomial K :=
  (north K).comp (LinearMap.fst K (Polynomial K) (Polynomial K)) +
    (south K).comp (LinearMap.snd K (Polynomial K) (Polynomial K))

/-- The polynomial pairs describing regular differential forms on the rational two-chart model. -/
def regularForms : Submodule K (Polynomial K × Polynomial K) := (overlap K).ker

private theorem coeff_nat (p : Polynomial K) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply (Nat.castEmbedding : ℕ ↪ ℤ).injective p.toFinsupp.coeff n

private theorem coeff_negative (p : Polynomial K) (n : ℤ) (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  change (m : ℤ) = n at hm
  have hnonneg : (0 : ℤ) ≤ n := hm ▸ Int.natCast_nonneg m
  omega

private theorem coeff_mul_T (p : LaurentPolynomial K) (n : ℤ) :
    (p * LaurentPolynomial.T (-2)).coeff n = p.coeff (n + 2) := by
  change (p * AddMonoidAlgebra.single (-2 : ℤ) (1 : K)).coeff n = _
  rw [AddMonoidAlgebra.coeff_mul_single_apply]
  simp

theorem regularForms_subsingleton : Subsingleton (regularForms K) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  have hz : z.val.1.toLaurent +
      LaurentPolynomial.invert z.val.2.toLaurent * LaurentPolynomial.T (-2) = 0 := z.property
  have hCoeff (n : ℤ) :
      z.val.1.toLaurent.coeff n + z.val.2.toLaurent.coeff (-(n + 2)) = 0 := by
    have hn := congrArg (fun p : LaurentPolynomial K => p.coeff n) hz
    simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_T,
      LaurentPolynomial.invert_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hn
  have hNorth : z.val.1 = 0 := by
    apply Polynomial.ext
    intro n
    have hneg : -((n : ℤ) + 2) < 0 := by omega
    have h := hCoeff (n : ℤ)
    rw [coeff_nat, coeff_negative K _ _ hneg, add_zero] at h
    simpa using h
  have hSouth : z.val.2 = 0 := by
    apply Polynomial.ext
    intro n
    have hneg : -(n : ℤ) - 2 < 0 := by omega
    have hshift : -((-(n : ℤ) - 2) + 2) = (n : ℤ) := by omega
    have h := hCoeff (-(n : ℤ) - 2)
    rw [coeff_negative K _ _ hneg, hshift, coeff_nat, zero_add] at h
    simpa using h
  exact Subtype.ext (Prod.ext hNorth hSouth)

/-- The genus obtained by dimension of regular differentials for the rational compactification. -/
def genus : ℕ := Module.finrank K (regularForms K)

theorem genus_eq_zero : genus K = 0 := by
  letI := regularForms_subsingleton K
  exact Module.finrank_zero_of_subsingleton

end

end ManuscriptAudit.RationalChartGenus

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.RationalChartGenus.regularForms_subsingleton,
      ``ManuscriptAudit.RationalChartGenus.genus_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
