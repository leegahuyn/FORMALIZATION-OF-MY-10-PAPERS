import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.SmoothGenericIntegral

/-!
# Integral factors of an affine étale algebra

The finite product of fields in the generic fiber provides coordinate
idempotents. They extend to the original algebra over an integrally
closed base. Each resulting quotient is a domain and is étale because
it is a localization at its lifted idempotent.
-/

namespace ManuscriptAudit.AffineEtaleDomainFactors

open scoped TensorProduct

noncomputable section

private theorem ker_eval_eq_span {B I : Type*} [CommRing B] [DecidableEq I]
    (L : I → Type*) [∀ i, CommRing (L i)] (g : B →+* ∀ i, L i)
    (hg : Function.Injective g) (e : I → B) (he : ∀ i, g (e i) = Pi.single i 1) (i : I) :
    RingHom.ker ((Pi.evalRingHom L i).comp g) = Ideal.span {1 - e i} := by
  ext b
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change g b i = 0 ↔ 1 - e i ∣ b
  constructor
  · intro hb
    have hzero : e i * b = 0 := hg (by
      rw [map_mul, he i, map_zero]
      funext j
      change Pi.single i (1 : L i) j * g b j = 0
      by_cases hj : j = i
      · subst j
        simp [hb]
      · simp [Pi.single_eq_of_ne hj])
    exact ⟨b, by rw [sub_mul, one_mul, hzero, sub_zero]⟩
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_sub, map_one, he i]
    change ((1 : L i) - Pi.single i (1 : L i) i) * g b i = 0
    simp

private theorem idempotentQuotientEtale (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] {e : B} (he : IsIdempotentElem e) :
    Algebra.Etale A (B ⧸ Ideal.span {1 - e}) := by
  let J : Ideal B := Ideal.span {1 - e}
  letI : IsLocalization.Away e (B ⧸ J) := IsLocalization.away_of_isIdempotentElem he (by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]) Ideal.Quotient.mk_surjective
  letI : Algebra.Etale B (B ⧸ J) := Algebra.Etale.of_isLocalizationAway e
  exact Algebra.Etale.comp A B (B ⧸ J)

universe u

set_option maxHeartbeats 900000 in
/-- The coordinate-ring quotient maps give a finite product decomposition
of an affine étale algebra into integral affine étale factors. -/
theorem exists_etale_domain_factors (A B F : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Nontrivial B] [Field F] [Algebra A B]
    [Algebra A F] [IsFractionRing A F] [Algebra.Etale A B] :
    ∃ (I : Type u) (_ : Finite I) (e : I → B),
      (∀ i, IsIdempotentElem (e i)) ∧
      (∀ i, IsDomain (B ⧸ Ideal.span {1 - e i})) ∧
      (∀ i, Algebra.Etale A (B ⧸ Ideal.span {1 - e i})) ∧
      Function.Bijective (RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  classical
  obtain ⟨I, hI, L, hL, hAlg, E, _⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod F (F ⊗[A] B)).mp inferInstance
  letI : Finite I := hI
  letI : Fintype I := Fintype.ofFinite I
  letI (i : I) : Field (L i) := hL i
  let er : B ⊗[A] F ≃+* (∀ i, L i) :=
    (Algebra.TensorProduct.comm A B F).toRingEquiv.trans E.toRingEquiv
  let g : B →+* (∀ i, L i) := er.toRingHom.comp (algebraMap B (B ⊗[A] F))
  have hg : Function.Injective g :=
    er.injective.comp (SmoothGenericIntegral.genericAlgebraMap_injective A B F)
  have hPi : CompleteOrthogonalIdempotents (fun i ↦ Pi.single i (1 : L i)) :=
    CompleteOrthogonalIdempotents.single L
  have hLift (i : I) : ∃ x : B, g x = Pi.single i 1 := by
    let z := er.symm (Pi.single i (1 : L i))
    have hz : z * z = z := er.injective (by
      rw [map_mul]
      simpa only [z, RingEquiv.apply_symm_apply] using (hPi.idem i).eq)
    obtain ⟨b, ⟨_, hb⟩, _⟩ := SmoothGenericIntegral.existsUnique_idempotent_section A B F z hz
    refine ⟨b, ?_⟩
    change er (algebraMap B (B ⊗[A] F) b) = _
    rw [hb]
    exact er.apply_symm_apply _
  choose e he using hLift
  have heC : CompleteOrthogonalIdempotents e := by
    apply (CompleteOrthogonalIdempotents.map_injective_iff g hg).mp
    have h : g ∘ e = (fun i ↦ Pi.single i (1 : L i)) := funext he
    rw [h]
    exact hPi
  refine ⟨I, hI, e, heC.idem, ?_, fun i ↦ idempotentQuotientEtale A B (heC.idem i),
    heC.bijective_pi⟩
  intro i
  apply Ideal.Quotient.isDomain_iff_prime.mpr
  rw [← ker_eval_eq_span L g hg e he i]
  exact RingHom.ker_isPrime ((Pi.evalRingHom L i).comp g)

end

end ManuscriptAudit.AffineEtaleDomainFactors

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineEtaleDomainFactors.exists_etale_domain_factors
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
