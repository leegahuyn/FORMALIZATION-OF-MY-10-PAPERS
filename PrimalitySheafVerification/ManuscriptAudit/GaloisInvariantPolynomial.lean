import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Descent of Galois-invariant homogeneous polynomials

A polynomial fixed under every automorphism of a Galois extension has
all coefficients in the base field. Coefficient descent preserves the
degree and evaluation on coordinates over the base field.
-/

namespace ManuscriptAudit.GaloisInvariantPolynomial

open MvPolynomial

noncomputable section

variable {F L σ : Type*} [Field F] [Field L] [Algebra F L] [IsGalois F L]

/-- An invariant homogeneous polynomial is the coefficient extension
of a homogeneous polynomial over the base field. -/
theorem exists_homogeneous_map_eq (Q : MvPolynomial σ L) {d : ℕ} (hQ : Q.IsHomogeneous d)
    [FiniteDimensional F L] (h : ∀ τ : L ≃ₐ[F] L, map τ.toRingHom Q = Q) :
    ∃ P : MvPolynomial σ F, P.IsHomogeneous d ∧ map (algebraMap F L) P = Q := by
  classical
  have hFix (m : σ →₀ ℕ) (τ : L ≃ₐ[F] L) : τ (Q.coeff m) = Q.coeff m := by
    have he := congrArg (MvPolynomial.coeff m) (h τ)
    rw [MvPolynomial.coeff_map] at he
    exact he
  have hBase (m : σ →₀ ℕ) : ∃ a : F, algebraMap F L a = Q.coeff m :=
    IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed (Q.coeff m)).2 (hFix m))
  choose c hc using hBase
  let P := ∑ m ∈ Q.support, monomial m (c m)
  refine ⟨P, ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro m hm
    apply isHomogeneous_monomial
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.mp hm)
  · change map (algebraMap F L) (∑ m ∈ Q.support, monomial m (c m)) = Q
    rw [map_sum]
    simp_rw [map_monomial, hc]
    exact Q.support_sum_monomial_coeff

/-- Base-field evaluation commutes with coefficient extension. -/
theorem aeval_map_algebraMap (P : MvPolynomial σ F) (z : σ → F) :
    aeval (fun i ↦ algebraMap F L (z i)) (map (algebraMap F L) P) =
      algebraMap F L (aeval z P) := by
  change eval ((algebraMap F L) ∘ z) (map (algebraMap F L) P) =
    algebraMap F L (eval z P)
  rw [eval_map]
  exact (eval₂_comp (algebraMap F L) z P).symm

end

end ManuscriptAudit.GaloisInvariantPolynomial

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisInvariantPolynomial.exists_homogeneous_map_eq,
      ``ManuscriptAudit.GaloisInvariantPolynomial.aeval_map_algebraMap] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
