import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The coordinate quotient of the cusp inclusion

Paper 2, p. 40, Proposition 3.24 uses a local δ contribution. This file
calculates the vector-space quotient of the coordinate inclusion
K[X²,X³] ⊂ K[X]. The coefficient of X identifies the quotient with K.
-/

namespace ManuscriptAudit.CuspDelta

open Polynomial

noncomputable section

variable (K : Type*) [Field K]

private abbrev cuspSubalgebra : Subalgebra K (Polynomial K) :=
  Algebra.adjoin K ({(X : Polynomial K) ^ 2, X ^ 3} : Set (Polynomial K))

private theorem pow_mem_cusp (n : ℕ) (hn : n ≠ 1) :
    (X : Polynomial K) ^ n ∈ cuspSubalgebra K := by
  have h2 : (X : Polynomial K) ^ 2 ∈ cuspSubalgebra K :=
    Algebra.subset_adjoin (by simp)
  have h3 : (X : Polynomial K) ^ 3 ∈ cuspSubalgebra K :=
    Algebra.subset_adjoin (by simp)
  by_cases heven : n % 2 = 0
  · have hform : n = 2 * (n / 2) := by omega
    rw [hform, pow_mul]
    exact (cuspSubalgebra K).pow_mem h2 _
  · have hform : n = 3 + 2 * ((n - 3) / 2) := by omega
    rw [hform, pow_add, pow_mul]
    exact (cuspSubalgebra K).mul_mem h3 ((cuspSubalgebra K).pow_mem h2 _)

private theorem cusp_mem_iff_coeff_one_zero (f : Polynomial K) :
    f ∈ cuspSubalgebra K ↔ f.coeff 1 = 0 := by
  constructor
  · intro hf
    refine Algebra.adjoin_induction (p := fun g _ => g.coeff 1 = 0) ?_ ?_ ?_ ?_ hf
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h | h <;> subst g <;> simp
    · intro a
      simp
    · intro g h _ _ hg hh
      simp [hg, hh]
    · intro g h _ _ hg hh
      simp [Polynomial.mul_coeff_one, hg, hh]
  · intro hf
    rw [← Polynomial.sum_C_mul_X_pow_eq f, Polynomial.sum]
    apply (cuspSubalgebra K).sum_mem
    intro n hn
    have hne : n ≠ 1 := by
      intro h
      subst n
      exact (Polynomial.mem_support_iff.mp hn) hf
    rw [Polynomial.C_eq_algebraMap]
    exact (cuspSubalgebra K).mul_mem ((cuspSubalgebra K).algebraMap_mem _)
      (pow_mem_cusp K n hne)

private theorem cusp_submodule_eq_ker :
    (cuspSubalgebra K).toSubmodule = (Polynomial.lcoeff K 1).ker := by
  ext f
  simpa only [Subalgebra.mem_toSubmodule, LinearMap.mem_ker, Polynomial.lcoeff_apply]
    using cusp_mem_iff_coeff_one_zero K f

private def cusp_quotient_equiv :
    (Polynomial K ⧸ (cuspSubalgebra K).toSubmodule) ≃ₗ[K] K := by
  rw [cusp_submodule_eq_ker]
  refine (Polynomial.lcoeff K 1).quotKerEquivOfSurjective ?_
  intro a
  exact ⟨Polynomial.monomial 1 a, by simp⟩

/-- The coordinate quotient of K[X²,X³] inside K[X] has dimension one. -/
theorem paper2_cusp_delta_coordinate_quotient_finrank :
    Module.finrank K
      (Polynomial K ⧸ (Algebra.adjoin K
        ({(X : Polynomial K) ^ 2, X ^ 3} : Set (Polynomial K))).toSubmodule) = 1 :=
  (LinearEquiv.finrank_eq (cusp_quotient_equiv K)).trans (Module.finrank_self K)

end

end ManuscriptAudit.CuspDelta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CuspDelta.paper2_cusp_delta_coordinate_quotient_finrank
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
