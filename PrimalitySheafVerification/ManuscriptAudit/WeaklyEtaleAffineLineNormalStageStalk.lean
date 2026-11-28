import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.Dvr
import PrimalitySheafVerification.ManuscriptAudit.AffineLineClosedPrimeResidue
import PrimalitySheafVerification.ManuscriptAudit.FiniteProductStageStalk
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineFiniteNormalization
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineStageUnramified

/-! At every image of the actual weakly étale chart, the finite
normal model has a valuation stalk and is unramified over the affine line. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineNormalStageStalk

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open WeaklyEtaleAffineLineGenericStage (F)
open WeaklyEtaleAffineLineFiniteNormalization (model model_finite component_dedekind)
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K

variable {ι : Type u} (L : ι → Type u) [Finite ι]
  [∀ i, Field (L i)] [∀ i, Algebra (F K) (L i)]
  [∀ i, Algebra (R K) (L i)] [∀ i, IsScalarTower (R K) (F K) (L i)]
  [∀ i, Module.Finite (F K) (L i)] [∀ i, Algebra.IsSeparable (F K) (L i)]

private theorem formallyEtale_component (i : ι) : Algebra.FormallyEtale (R K) (L i) := by
  letI : Algebra.FormallyEtale (R K) (F K) := Algebra.FormallyEtale.of_isLocalization (R K)⁰
  letI : Algebra.FormallyEtale (F K) (L i) :=
    (Algebra.FormallyEtale.iff_isSeparable (F K) (L i)).mpr inferInstance
  exact Algebra.FormallyEtale.comp (R K) (F K) (L i)

private theorem valuation_of_equiv {S T : Type u} [CommRing S] [CommRing T]
    [IsDomain S] [IsDomain T] [ValuationRing T] (e : S ≃+* T) : ValuationRing S := by
  apply ValuationRing.iff_dvd_total.mpr
  refine ⟨fun x y ↦ ?_⟩
  have h {a b : S} (h : e a ∣ e b) : a ∣ b := by
    obtain ⟨c, hc⟩ := h
    exact ⟨e.symm c, e.injective (by rw [map_mul, e.apply_symm_apply, hc])⟩
  exact (ValuationRing.dvd_total (e x) (e y)).imp h h

set_option maxHeartbeats 2400000 in
/-- The local normal model at the image of any actual chart prime is
a valuation ring and is unramified, also above the generic point. -/
theorem local_properties (g : model K L →ₐ[R K] B) (r : Ideal B) [r.IsPrime] :
    let q := r.comap g.toRingHom
    ∃ hD : IsDomain (Localization.AtPrime q),
      letI := hD
      ValuationRing (Localization.AtPrime q) ∧ Algebra.IsUnramifiedAt (R K) q := by
  let D := model K L
  let q := r.comap g.toRingHom
  let p := q.comap (algebraMap (R K) D)
  letI : q.IsPrime := Ideal.IsPrime.comap g.toRingHom
  letI : p.IsPrime := Ideal.IsPrime.comap (algebraMap (R K) D)
  letI : q.LiesOver p := ⟨rfl⟩
  let C : ι → Type u := fun i ↦ integralClosure (R K) (L i)
  let Q : PrimeSpectrum (∀ i, C i) := ⟨q, ‹q.IsPrime›⟩
  obtain ⟨i, P, hQ, ⟨e⟩⟩ := FiniteProductStageStalk.exists_component (R K) C Q
  let S := Localization.AtPrime P.asIdeal
  have hP : P.asIdeal.comap (algebraMap (R K) (C i)) = p := by
    have hq := congrArg PrimeSpectrum.asIdeal hQ
    change q = P.asIdeal.comap (Pi.evalRingHom C i) at hq
    unfold p
    rw [hq, Ideal.comap_comap] <;> rfl
  letI : IsDomain (Localization.AtPrime q) :=
    Function.Injective.isDomain e.toRingEquiv e.injective
  refine ⟨inferInstance, ?_⟩
  by_cases hp : p = ⊥
  · have hP₀ : P.asIdeal = ⊥ := Ideal.eq_bot_of_comap_eq_bot (hP.trans hp)
    letI : IsFractionRing (C i) S := by
      change IsLocalization (C i)⁰ (Localization.AtPrime P.asIdeal)
      have hCompl : P.asIdeal.primeCompl = (C i)⁰ := by
        ext a
        change (a ∉ P.asIdeal) ↔ a ∈ (C i)⁰
        rw [hP₀, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
      exact hCompl ▸ (inferInstance : IsLocalization P.asIdeal.primeCompl S)
    letI : IsFractionRing (C i) (L i) :=
      IsIntegralClosure.isFractionRing_of_finite_extension (R K) (F K) (L i) (C i)
    let e₀ : S ≃ₐ[C i] L i := IsLocalization.algEquiv (C i)⁰ _ _
    let e₁ := e.trans (e₀.restrictScalars (R K))
    letI : Algebra.FormallyEtale (R K) (L i) := formallyEtale_component K L i
    letI : Algebra.FormallyEtale (R K) (Localization.AtPrime q) :=
      Algebra.FormallyEtale.of_equiv e₁.symm
    exact ⟨valuation_of_equiv e₁.toRingEquiv, inferInstance⟩
  · have hP₀ : P.asIdeal ≠ ⊥ := by
      intro h
      apply hp
      calc
        _ = P.asIdeal.comap (algebraMap (R K) (C i)) := hP.symm
        _ = ⊥ := by
          rw [h, ← RingHom.ker_eq_comap_bot]
          apply (RingHom.injective_iff_ker_eq_bot (algebraMap (R K) (C i))).mp
          have hL : Function.Injective (algebraMap (R K) (L i)) := by
            rw [IsScalarTower.algebraMap_eq (R K) (F K) (L i)]
            exact (RingHom.injective _).comp (IsFractionRing.injective (R K) (F K))
          intro x y hxy
          apply hL
          simpa only [IsScalarTower.algebraMap_apply (R K) (C i) (L i)] using
            congrArg (algebraMap (C i) (L i)) hxy
    letI : IsDedekindDomain (C i) := component_dedekind K L i
    letI : IsDiscreteValuationRing S :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (C i) hP₀ S
    letI : IsPrincipalIdealRing (Localization.AtPrime q) :=
      IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
    letI : IsDiscreteValuationRing (Localization.AtPrime q) := by
      constructor
      intro h
      apply IsDiscreteValuationRing.not_a_field S
      apply bot_unique
      intro x hx
      have hne : ¬ IsUnit x := by
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
      have hm : e.symm x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply hne
        exact e.apply_symm_apply x ▸ hu.map e.toRingEquiv.toRingHom
      have hx₀ : e.symm x = 0 := Ideal.mem_bot.mp (h ▸ hm)
      exact Ideal.mem_bot.mpr (e.symm.injective (hx₀.trans (map_zero e.symm).symm))
    letI : Module.Finite (R K) D := model_finite K L
    letI := Localization.AtPrime.algebraOfLiesOver p q
    let t := Submodule.IsPrincipal.generator p
    have ht : Prime t := Submodule.IsPrincipal.prime_generator_of_isPrime p hp
    have hpg : p = Ideal.span ({t} : Set (R K)) := (Ideal.span_singleton_generator p).symm
    have hSep := AffineLineClosedPrimeResidue.finite_residue_separable K p hp q
    exact ⟨inferInstance,
      WeaklyEtaleAffineLineStageUnramified.isUnramifiedAt g p q r rfl t ht hpg hSep⟩

end
end ManuscriptAudit.WeaklyEtaleAffineLineNormalStageStalk

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineNormalStageStalk.local_properties
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
