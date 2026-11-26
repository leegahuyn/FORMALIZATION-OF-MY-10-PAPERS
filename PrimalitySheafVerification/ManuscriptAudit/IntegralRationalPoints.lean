import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Rational labeling of the primes of an integral algebra

Over an algebraically closed field, a prime of an integral algebra is
the kernel of a unique rational point. The equivalence uses the actual
quotient by the prime, so it applies to each residue-field fiber of an
étale morphism.
-/

namespace ManuscriptAudit.IntegralRationalPoints

noncomputable section

variable (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
  [Algebra.IsIntegral K B]

private def scalarQuotientIso (p : PrimeSpectrum B) : K ≃ₐ[K] (B ⧸ p.asIdeal) := by
  let Q := B ⧸ p.asIdeal
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : Algebra.IsIntegral K Q := ⟨fun z ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact (Algebra.IsIntegral.isIntegral (R := K) b).map (Ideal.Quotient.mkₐ K p.asIdeal)⟩
  exact AlgEquiv.ofBijective (Algebra.ofId K Q)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))

/-- Evaluation at the rational point with the stated prime kernel. -/
def evalAtPrime (p : PrimeSpectrum B) : B →ₐ[K] K :=
  (scalarQuotientIso K B p).symm.toAlgHom.comp (Ideal.Quotient.mkₐ K p.asIdeal)

@[simp] theorem ker_evalAtPrime (p : PrimeSpectrum B) :
    RingHom.ker (evalAtPrime K B p) = p.asIdeal := by
  let e := scalarQuotientIso K B p
  ext b
  rw [RingHom.mem_ker]
  change e.symm (Ideal.Quotient.mk p.asIdeal b) = 0 ↔ _
  rw [← map_zero e.symm]
  exact e.symm.injective.eq_iff.trans Ideal.Quotient.eq_zero_iff_mem

/-- The actual rational points of an integral algebra over an algebraically
closed field are indexed by precisely its prime ideals. -/
def primeSpectrumEquivAlgHom : PrimeSpectrum B ≃ (B →ₐ[K] K) where
  toFun := evalAtPrime K B
  invFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  left_inv p := PrimeSpectrum.ext (ker_evalAtPrime K B p)
  right_inv f := by
    apply AlgHom.ext
    intro b
    let p : PrimeSpectrum B := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
    let e := scalarQuotientIso K B p
    let f' := Ideal.kerLiftAlg f
    have h (z : B ⧸ p.asIdeal) : e.symm z = f' z := by
      obtain ⟨k, rfl⟩ := e.surjective z
      rw [e.symm_apply_apply]
      exact (f'.commutes k).symm
    change e.symm (Ideal.Quotient.mk p.asIdeal b) = f b
    exact (h _).trans (Ideal.kerLiftAlg_mk f b)

end

end ManuscriptAudit.IntegralRationalPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralRationalPoints.ker_evalAtPrime,
      ``ManuscriptAudit.IntegralRationalPoints.primeSpectrumEquivAlgHom] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
