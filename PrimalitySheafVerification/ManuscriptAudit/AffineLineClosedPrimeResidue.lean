import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Polynomial.Quotient

/-! The actual residue field of a closed point of the affine line
over an algebraically closed field is algebraically closed. -/

namespace ManuscriptAudit.AffineLineClosedPrimeResidue

open Polynomial IsDedekindDomain

noncomputable section

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

private abbrev R := Polynomial K

/-- A nonzero prime has the actual residue field of a rational coordinate. -/
theorem isAlgClosed (p : Ideal (R K)) [p.IsPrime] (hp : p ≠ ⊥) :
    IsAlgClosed p.ResidueField := by
  let t := Submodule.IsPrincipal.generator p
  have ht : Prime t := Submodule.IsPrincipal.prime_generator_of_isPrime p hp
  have hdeg : t.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K ht.irreducible]
    exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root t hdeg
  have hAssoc : Associated (X - C a) t :=
    (irreducible_X_sub_C a).associated_of_dvd ht.irreducible ((dvd_iff_isRoot).mpr ha)
  have hspan : p = Ideal.span ({X - C a} : Set (R K)) :=
    (Ideal.span_singleton_generator p).symm.trans
      (Ideal.span_singleton_eq_span_singleton.mpr hAssoc.symm)
  let e₀ : (R K ⧸ p) ≃+* K :=
    (Ideal.quotEquivOfEq hspan).trans (quotientSpanXSubCAlgEquiv a).toRingEquiv
  letI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  let e₁ : (R K ⧸ p) ≃+* p.ResidueField :=
    RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField p)
  exact IsAlgClosed.of_ringEquiv K p.ResidueField (e₀.symm.trans e₁)

/-- In a finite actual stage, residue extensions above the closed
points of the affine line are separable. -/
theorem finite_residue_separable {C : Type u} [CommRing C] [Algebra (R K) C]
    [Module.Finite (R K) C]
    (p : Ideal (R K)) [p.IsPrime] (hp : p ≠ ⊥)
    (q : Ideal C) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Algebra.IsSeparable p.ResidueField q.ResidueField := by
  letI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  letI : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q p
  letI : IsAlgClosed p.ResidueField := isAlgClosed K p hp
  letI : Module.Finite (R K) q.ResidueField := Module.Finite.trans C q.ResidueField
  letI : Module.Finite p.ResidueField q.ResidueField :=
    Module.Finite.of_restrictScalars_finite (R K) p.ResidueField q.ResidueField
  infer_instance

end
end ManuscriptAudit.AffineLineClosedPrimeResidue

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineClosedPrimeResidue.isAlgClosed,
      ``ManuscriptAudit.AffineLineClosedPrimeResidue.finite_residue_separable] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
