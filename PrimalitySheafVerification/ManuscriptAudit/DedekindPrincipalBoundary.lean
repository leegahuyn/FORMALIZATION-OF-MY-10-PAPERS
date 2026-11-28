import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! Adding a single closed prime point with a principal ideal to a
Dedekind open preserves the Dedekind property. -/

namespace ManuscriptAudit.DedekindPrincipalBoundary

open scoped nonZeroDivisors

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

private theorem atPrime_dvr_of_principal (P : Ideal R) [P.IsPrime]
    (hP : P ≠ ⊥) (hPrincipal : P.IsPrincipal) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let L := Localization.AtPrime P
  letI : IsNoetherianRing L := IsLocalization.isNoetherianRing P.primeCompl L inferInstance
  have hNF : ¬ IsField L := IsLocalization.AtPrime.not_isField R hP L
  have hM : (IsLocalRing.maximalIdeal L).IsPrincipal := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact hPrincipal.map_ringHom (algebraMap R L)
  exact ((IsDiscreteValuationRing.TFAE L hNF).out 0 4).mpr hM

private theorem atPrime_dvr_from_open {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Algebra R S] (d : R) [IsLocalization.Away d S] (hd : d ≠ 0)
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (hNot : d ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let J := P.map (algebraMap R S)
  have hDisjoint : Disjoint (Submonoid.powers d : Set R) (P : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime d).mpr hNot
  letI : J.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers d) S P ‹_› hDisjoint
  have hJ : J ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective (M := Submonoid.powers d) S
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd))).not.mpr hP
  let T := Localization.AtPrime J
  let L := Localization.AtPrime P
  have hUnder : J.under R = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers d) S ‹_› hDisjoint
  letI : IsLocalization.AtPrime T P :=
    hUnder ▸ IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers d) T J
  let e : T ≃+* L := (IsLocalization.algEquiv P.primeCompl T L).toRingEquiv
  letI : IsDiscreteValuationRing T :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hJ T
  letI : IsPrincipalIdealRing L := IsPrincipalIdealRing.of_surjective e e.surjective
  letI : IsNoetherianRing L := IsLocalization.isNoetherianRing P.primeCompl L inferInstance
  have hNF : ¬ IsField L := IsLocalization.AtPrime.not_isField R hP L
  exact ((IsDiscreteValuationRing.TFAE L hNF).out 0 4).mpr inferInstance

/-- A Noetherian domain is Dedekind when a principal open is Dedekind
and every prime omitted from the open has a principal ideal. -/
theorem of_open {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S]
    (d : R) [IsLocalization.Away d S] (hd : d ≠ 0)
    (hBoundary : ∀ P : Ideal R, P.IsPrime → d ∈ P → P.IsPrincipal) :
    IsDedekindDomain R := by
  letI : IsDedekindDomainDvr R where
    is_dvr_at_nonzero_prime P hP hPrime := by
      letI : P.IsPrime := hPrime
      by_cases hdP : d ∈ P
      · exact atPrime_dvr_of_principal P hP (hBoundary P hPrime hdP)
      · exact atPrime_dvr_from_open (S := S) d hd P hP hdP
  infer_instance

end

end ManuscriptAudit.DedekindPrincipalBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.DedekindPrincipalBoundary.of_open
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
