import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDomainFactors

/-!
# Domain charts cover a disconnected affine étale scheme

The idempotent quotient factors are actual principal-open localizations.
Their basic opens cover the spectrum, including when the original
affine étale scheme is empty.
-/

namespace ManuscriptAudit.AffineEtaleDomainFactors

open scoped BigOperators

noncomputable section

universe u

private theorem basicOpens_cover_of_injective_quotients {I B : Type*} [Fintype I] [CommRing B]
    (e : I → B) (h : Function.Injective (RingHom.pi
      fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i}))) :
    ∀ x : PrimeSpectrum B, ∃ i, x ∈ PrimeSpectrum.basicOpen (e i) := by
  classical
  let q := RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i})
  have hz : (∏ i, (1 - e i)) = 0 := h (by
    funext i
    let g := Ideal.Quotient.mk (Ideal.span {1 - e i})
    change g (∏ j, (1 - e j)) = g 0
    rw [map_prod, map_zero]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))))
  intro x
  by_contra! hNone
  have hUnit (i : I) : 1 - e i ∉ x.asIdeal := by
    intro hi
    have hm : e i ∈ x.asIdeal := Classical.byContradiction (fun hn ↦ hNone i hn)
    exact x.isPrime.one_notMem (by
      simpa only [sub_add_cancel] using x.asIdeal.add_mem hi hm)
  have hProd (s : Finset I) : (∏ i ∈ s, (1 - e i)) ∉ x.asIdeal := by
    induction s using Finset.induction_on with
    | empty => simpa using x.isPrime.one_notMem
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact x.isPrime.mul_notMem (hUnit i) ih
  exact hProd Finset.univ (hz.symm ▸ x.asIdeal.zero_mem)

/-- Any affine étale algebra over an integrally closed domain has an
actual cover by principal-open domain charts. -/
theorem exists_etale_domain_cover (A B F : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Field F] [Algebra A B]
    [Algebra A F] [IsFractionRing A F] [Algebra.Etale A B] :
    ∃ (I : Type u) (_ : Finite I) (e : I → B),
      (∀ i, IsDomain (B ⧸ Ideal.span {1 - e i})) ∧
      (∀ i, Algebra.Etale A (B ⧸ Ideal.span {1 - e i})) ∧
      (∀ i, IsLocalization.Away (e i) (B ⧸ Ideal.span {1 - e i})) ∧
      (∀ x : PrimeSpectrum B, ∃ i, x ∈ PrimeSpectrum.basicOpen (e i)) := by
  cases subsingleton_or_nontrivial B with
  | inl h =>
    letI : Subsingleton B := h
    exact ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim, PEmpty.elim,
      fun x ↦ (x.isPrime.one_notMem ((Subsingleton.elim (1 : B) 0).symm ▸ x.asIdeal.zero_mem)).elim⟩
  | inr h =>
    letI : Nontrivial B := h
    obtain ⟨I, hI, e, he, hd, het, hb⟩ := exists_etale_domain_factors A B F
    letI : Finite I := hI
    letI : Fintype I := Fintype.ofFinite I
    refine ⟨I, hI, e, hd, het, ?_, basicOpens_cover_of_injective_quotients e hb.1⟩
    intro i
    exact IsLocalization.away_of_isIdempotentElem (he i)
      (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]) Ideal.Quotient.mk_surjective

end

end ManuscriptAudit.AffineEtaleDomainFactors

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineEtaleDomainFactors.exists_etale_domain_cover
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
