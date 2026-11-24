import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Picard groups of the cusp comparison's two smooth affine coordinate rings

The polynomial ring and its localization at its variable are both
principal ideal domains. Their algebraic Picard groups are trivial.
-/

namespace ManuscriptAudit.CuspPicard

open scoped nonZeroDivisors

/-- Triviality of the algebraic Picard group of the affine line. -/
theorem paper2_polynomial_picard_trivial (K : Type*) [Field K] :
    Subsingleton (CommRing.Pic (Polynomial K)) := by infer_instance

/-- Triviality of the algebraic Picard group of the multiplicative group. -/
theorem paper2_laurent_picard_trivial (K : Type*) [Field K] :
    Subsingleton (CommRing.Pic (LaurentPolynomial K)) := by
  let M := Submonoid.powers (Polynomial.X : Polynomial K)
  have hM : M ≤ (Polynomial K)⁰ := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  letI : IsDomain (LaurentPolynomial K) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (LaurentPolynomial K) hM
  letI : IsPrincipalIdealRing (LaurentPolynomial K) := ⟨fun I => by
    rw [← IsLocalization.map_under M (LaurentPolynomial K) I]
    exact Submodule.IsPrincipal.map_ringHom (algebraMap (Polynomial K) (LaurentPolynomial K))
      (inferInstance : (I.under (Polynomial K)).IsPrincipal)⟩
  infer_instance

/-- On the affine line over an algebraically closed field, every
unit is a d-th power for every positive d. -/
theorem paper2_polynomial_unit_power_surjective (K : Type*) [Field K] [IsAlgClosed K]
    (d : ℕ) (hd : 0 < d) : Function.Surjective (fun u : (Polynomial K)ˣ => u ^ d) := by
  intro u
  obtain ⟨a, ha, he⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hd
  have hbn : b ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hb
    exact ha.ne_zero hb.symm
  refine ⟨Units.map (Polynomial.C (R := K)).toMonoidHom (Units.mk0 b hbn), ?_⟩
  apply Units.ext
  change Polynomial.C b ^ d = (u : Polynomial K)
  rw [← map_pow, hb, he]

end ManuscriptAudit.CuspPicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspPicard.paper2_polynomial_picard_trivial,
      ``ManuscriptAudit.CuspPicard.paper2_laurent_picard_trivial,
      ``ManuscriptAudit.CuspPicard.paper2_polynomial_unit_power_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
