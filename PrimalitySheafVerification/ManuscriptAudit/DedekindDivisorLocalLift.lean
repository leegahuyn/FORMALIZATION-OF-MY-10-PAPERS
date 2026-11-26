import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import PrimalitySheafVerification.ManuscriptAudit.DedekindPrincipalDivisor

/-!
# Local lifts of finite cycles on an integral affine chart

A uniformizer produces any desired coefficient at one height-one
point. The remaining difference is finite and can be removed by one
principal open containing the given point.
-/

namespace ManuscriptAudit.DedekindPrincipalDivisor

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The actual principal-divisor coefficient at a height-one point
takes every integral value. -/
theorem principalDivisor_coefficient_surjective (p : HeightOneSpectrum R) :
    Function.Surjective (fun u : Additive Fˣ ↦ principalDivisor R F u p) := by
  classical
  obtain ⟨t, ht⟩ := p.intValuation_exists_uniformizer
  have ht₀ : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    rw [eq_comm] at ht
    simpa only [WithZero.exp_ne_zero] using ht
  have ht' : (Ideal.span {t} : Ideal R) ≠ 0 := by
    rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    exact ht₀
  let u := Additive.ofMul (Units.mk0 (algebraMap R F t)
    ((map_ne_zero_iff (algebraMap R F) (IsFractionRing.injective R F)).mpr ht₀))
  have h : principalDivisor R F u p = 1 := by
    change FractionalIdeal.count F p (FractionalIdeal.spanSingleton R⁰ (algebraMap R F t)) = 1
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F p ht']
    rwa [p.intValuation_if_neg ht₀, WithZero.exp_inj, neg_inj] at ht
  let coeff : Additive Fˣ →+ ℤ :=
    { toFun := fun z ↦ principalDivisor R F z p
      map_zero' := by simp
      map_add' := fun _ _ ↦ by simp }
  intro n
  refine ⟨n • u, ?_⟩
  change coeff (n • u) = n
  rw [map_zsmul, show coeff u = 1 from h, zsmul_eq_mul, mul_one]

private theorem finite_set_avoided (x : PrimeSpectrum R) (s : Finset (HeightOneSpectrum R))
    (h : ∀ p ∈ s, p.asIdeal ≠ x.asIdeal) :
    ∃ f : R, f ∉ x.asIdeal ∧ ∀ p ∈ s, f ∈ p.asIdeal := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, x.isPrime.one_notMem, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨f, hf, hs⟩ := ih (fun q hq ↦ h q (Finset.mem_insert_of_mem hq))
    have hpm : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal p.isPrime p.ne_bot
    have hle : ¬p.asIdeal ≤ x.asIdeal := by
      intro hg
      exact h p (Finset.mem_insert_self p s) (hpm.eq_of_le x.isPrime.ne_top hg)
    have hg : ∃ g : R, g ∈ p.asIdeal ∧ g ∉ x.asIdeal := by
      by_contra! he
      exact hle (fun g hg ↦ he g hg)
    obtain ⟨g, hgp, hgx⟩ := hg
    refine ⟨g * f, x.isPrime.mul_notMem hgx hf, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Ideal.mul_mem_right f _ hgp
    · exact Ideal.mul_mem_left _ g (hs q hq)

/-- Every finite cycle admits a lift by a fraction-field unit after
restricting to a principal open containing any specified point. -/
theorem exists_principalOpen_divisorLift (x : PrimeSpectrum R) (d : HeightOneSpectrum R →₀ ℤ) :
    ∃ (f : R) (_ : f ∉ x.asIdeal) (u : Additive Fˣ),
      ∀ q : HeightOneSpectrum R, f ∉ q.asIdeal → principalDivisor R F u q = d q := by
  classical
  have hMatch : ∃ u : Additive Fˣ, ∀ q : HeightOneSpectrum R, q.asIdeal = x.asIdeal →
      principalDivisor R F u q = d q := by
    by_cases hx : x.asIdeal = ⊥
    · exact ⟨0, fun q hq ↦ (q.ne_bot (hq.trans hx)).elim⟩
    · let p : HeightOneSpectrum R := ⟨x.asIdeal, x.isPrime, hx⟩
      obtain ⟨u, hu⟩ := principalDivisor_coefficient_surjective R F p (d p)
      refine ⟨u, fun q hq ↦ ?_⟩
      have he : q = p := HeightOneSpectrum.ext hq
      rw [he]
      exact hu
  obtain ⟨u, hu⟩ := hMatch
  let e := principalDivisor R F u - d
  have hSupport (q : HeightOneSpectrum R) (hq : q ∈ e.support) : q.asIdeal ≠ x.asIdeal := by
    intro hq'
    exact Finsupp.mem_support_iff.mp hq (sub_eq_zero.mpr (hu q hq'))
  obtain ⟨f, hf, h⟩ := finite_set_avoided R x e.support hSupport
  refine ⟨f, hf, u, fun q hq ↦ ?_⟩
  have hz : e q = 0 := Finsupp.notMem_support_iff.mp (fun hq' ↦ hq (h q hq'))
  exact sub_eq_zero.mp hz

end

end ManuscriptAudit.DedekindPrincipalDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindPrincipalDivisor.principalDivisor_coefficient_surjective,
      ``ManuscriptAudit.DedekindPrincipalDivisor.exists_principalOpen_divisorLift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
