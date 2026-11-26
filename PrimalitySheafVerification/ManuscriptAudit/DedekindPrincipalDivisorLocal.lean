import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.Dvr
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalDivisor

/-!
# Local surjectivity of the principal divisor map

In a principal ideal domain each finite cycle is associated to one
fraction-field unit. In particular this holds in the actual localization
of a Dedekind domain at a nonzero prime, which is a discrete valuation ring.
-/

namespace ManuscriptAudit.DedekindPrincipalDivisor

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

/-- Over a principal ideal domain, every finite divisor is principal. -/
theorem principalDivisor_surjective (R F : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] :
    Function.Surjective (principalDivisor R F) := by
  intro d
  obtain ⟨I, hI, hd⟩ := idealCycle_surjective_nonzero R F d
  let x : F := Submodule.IsPrincipal.generator (I : Submodule R F)
  have hSpan : I = FractionalIdeal.spanSingleton R⁰ x :=
    FractionalIdeal.eq_spanSingleton_of_principal I
  have hx : x ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mp (hSpan ▸ hI)
  refine ⟨Additive.ofMul (Units.mk0 x hx), ?_⟩
  change idealCycle R F (FractionalIdeal.spanSingleton R⁰ x) = d
  exact hSpan ▸ hd

/-- Divisors over a local chart of a Dedekind domain at a nonzero prime
are represented by fraction-field units. -/
theorem localPrincipalDivisor_surjective (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    Function.Surjective
      (principalDivisor (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))) := by
  let S := Localization.AtPrime p
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp S
  exact principalDivisor_surjective S (FractionRing S)

end

end ManuscriptAudit.DedekindPrincipalDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindPrincipalDivisor.principalDivisor_surjective,
      ``ManuscriptAudit.DedekindPrincipalDivisor.localPrincipalDivisor_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
