import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Normalized orders under étale restriction

An unramified local homomorphism of discrete valuation rings carries a
uniformizer to a uniformizer, so it preserves the normalized additive
order. This applies to the actual local rings at height-one points of an
étale morphism of Dedekind rings.
-/

namespace ManuscriptAudit.EtaleDivisorOrder

open IsDedekindDomain IsDiscreteValuationRing IsLocalRing

noncomputable section

/-- Mapping the maximal ideal to the maximal ideal preserves the normalized
order of every element. -/
theorem addVal_algebraMap_of_map_maximalIdeal (R S : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) (r : R) :
    addVal S (algebraMap R S r) = addVal R r := by
  by_cases hr : r = 0
  · subst r
    rw [map_zero, addVal_zero, addVal_zero]
  obtain ⟨t, ht⟩ := exists_irreducible R
  have ht' : Irreducible (algebraMap R S t) := by
    apply (irreducible_iff_uniformizer (algebraMap R S t)).mpr
    rw [← h, ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨n, u, hru⟩ := eq_unit_mul_pow_irreducible hr ht
  let v := Units.map (algebraMap R S).toMonoidHom u
  have hrv : algebraMap R S r = (v : S) * (algebraMap R S t) ^ n := by
    change algebraMap R S r = algebraMap R S (u : R) * (algebraMap R S t) ^ n
    simpa only [map_mul, map_pow] using congrArg (algebraMap R S) hru
  exact (addVal_def _ v ht' n hrv).trans (addVal_def r u ht n hru).symm

section Localizations

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]
  (p : HeightOneSpectrum R) (q : HeightOneSpectrum S) [q.asIdeal.LiesOver p.asIdeal]

private local instance dvrAtHeightOne {D : Type*} [CommRing D] [IsDomain D]
    [IsDedekindDomain D] (x : HeightOneSpectrum D) :
    IsDiscreteValuationRing (Localization.AtPrime x.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain D x.ne_bot _

/-- The actual map on localizations at height-one points of an étale algebra
preserves normalized order. -/
theorem localRingHom_addVal (r : Localization.AtPrime p.asIdeal) :
    addVal (Localization.AtPrime q.asIdeal)
      (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S)
        (Ideal.LiesOver.over : p.asIdeal = q.asIdeal.comap (algebraMap R S)) r) =
      addVal (Localization.AtPrime p.asIdeal) r := by
  let RP := Localization.AtPrime p.asIdeal
  let SQ := Localization.AtPrime q.asIdeal
  letI : Algebra RP SQ := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  letI : IsLocalHom (algebraMap RP SQ) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    infer_instance
  letI : Algebra.EssFiniteType RP SQ := Algebra.EssFiniteType.of_comp R RP SQ
  letI : Algebra.FormallyUnramified R SQ :=
    inferInstanceAs (Algebra.FormallyUnramified R (Localization q.asIdeal.primeCompl))
  letI : Algebra.FormallyUnramified RP SQ := Algebra.FormallyUnramified.of_restrictScalars R RP SQ
  change addVal SQ (algebraMap RP SQ r) = _
  exact addVal_algebraMap_of_map_maximalIdeal RP SQ
    Algebra.FormallyUnramified.map_maximalIdeal r

end Localizations

end

end ManuscriptAudit.EtaleDivisorOrder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleDivisorOrder.addVal_algebraMap_of_map_maximalIdeal,
      ``ManuscriptAudit.EtaleDivisorOrder.localRingHom_addVal] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
