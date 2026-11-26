import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Principal divisors over a Dedekind domain

The arithmetic of fractional ideals gives a finitely supported integer
valuation at every height-one prime. The corresponding homomorphism on
fraction-field units has as kernel exactly the original ring units.
This construction also applies to normal affine curves with nonprincipal
divisors.
-/

namespace ManuscriptAudit.DedekindPrincipalDivisor

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The finite cycle of a fractional ideal, using its native ideal valuations. -/
def idealCycle (I : FractionalIdeal R⁰ F) : HeightOneSpectrum R →₀ ℤ := by
  classical
  let h := FractionalIdeal.finite_factors I
  exact Finsupp.mk h.toFinset (fun v => FractionalIdeal.count F v I) (fun _ => h.mem_toFinset)

theorem idealCycle_apply (I : FractionalIdeal R⁰ F) (v : HeightOneSpectrum R) :
    idealCycle R F I v = FractionalIdeal.count F v I := rfl

/-- Every finite integral cycle comes from a nonzero fractional ideal. -/
theorem idealCycle_surjective_nonzero (d : HeightOneSpectrum R →₀ ℤ) :
    ∃ I : FractionalIdeal R⁰ F, I ≠ 0 ∧ idealCycle R F I = d := by
  let I := d.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ F) ^ n)
  refine ⟨I, ?_, ?_⟩
  · change (∏ v ∈ d.support, (v.asIdeal : FractionalIdeal R⁰ F) ^ d v) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun v _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  · apply Finsupp.ext
    intro v
    exact FractionalIdeal.count_finsuppProd F v d

/-- The divisor at the height-one primes of a fraction-field unit. -/
def principalDivisor : Additive Fˣ →+ (HeightOneSpectrum R →₀ ℤ) where
  toFun x := idealCycle R F (FractionalIdeal.spanSingleton R⁰ (x.toMul : F))
  map_zero' := by
    apply Finsupp.ext
    intro v
    change FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (1 : F)) = 0
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  map_add' x y := by
    let a : F := x.toMul
    let b : F := y.toMul
    apply Finsupp.ext
    intro v
    change FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (a * b)) =
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ a) +
        FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ b)
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
    exact FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.toMul.ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.toMul.ne_zero)

/-- The inclusion of units of the original domain into the fraction field. -/
def unitInclusion : Additive Rˣ →+ Additive Fˣ :=
  (Units.map (algebraMap R F).toMonoidHom).toAdditive

theorem unitInclusion_injective : Function.Injective (unitInclusion R F) := by
  intro x y h
  apply Additive.ext
  apply Units.ext
  apply IsFractionRing.injective R F
  exact congrArg (fun u : Additive Fˣ => (u.toMul : F)) h

/-- A fraction-field unit has zero divisor exactly when it is a ring unit. -/
theorem principalDivisor_exact : Function.Exact (unitInclusion R F) (principalDivisor R F) := by
  intro x
  let I := FractionalIdeal.spanSingleton R⁰ (x.toMul : F)
  constructor
  · intro h
    have hv (v : HeightOneSpectrum R) : FractionalIdeal.count F v I = 0 :=
      congrArg (fun d : HeightOneSpectrum R →₀ ℤ => d v) h
    have hI : I ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.toMul.ne_zero
    have hOne : I = 1 := by
      rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI]
      simp [hv]
    have hSpan : FractionalIdeal.spanSingleton R⁰ (1 : F) = I :=
      FractionalIdeal.spanSingleton_one.trans hOne.symm
    obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 hSpan
    refine ⟨Additive.ofMul u, ?_⟩
    apply Additive.ext
    apply Units.ext
    change algebraMap R F (u : R) = (x.toMul : F)
    change (u : R) • (1 : F) = (x.toMul : F) at hu
    rw [← Algebra.algebraMap_eq_smul_one] at hu
    exact hu
  · rintro ⟨u, rfl⟩
    have hSpan : FractionalIdeal.spanSingleton R⁰ (1 : F) =
        FractionalIdeal.spanSingleton R⁰ (algebraMap R F (u.toMul : R)) := by
      apply FractionalIdeal.spanSingleton_eq_spanSingleton.2
      refine ⟨u.toMul, ?_⟩
      change (u.toMul : R) • (1 : F) = algebraMap R F (u.toMul : R)
      exact (Algebra.algebraMap_eq_smul_one (u.toMul : R)).symm
    apply Finsupp.ext
    intro v
    change FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton R⁰ (algebraMap R F (u.toMul : R))) = 0
    rw [← hSpan, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

end

end ManuscriptAudit.DedekindPrincipalDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindPrincipalDivisor.idealCycle_surjective_nonzero,
      ``ManuscriptAudit.DedekindPrincipalDivisor.unitInclusion_injective,
      ``ManuscriptAudit.DedekindPrincipalDivisor.principalDivisor_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
