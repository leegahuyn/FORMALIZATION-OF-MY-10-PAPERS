import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.DoubleCoverTopologicalTrace
import PrimalitySheafVerification.ManuscriptAudit.InvolutionSpectrumOrbits
import PrimalitySheafVerification.ManuscriptAudit.InvolutionTensorComparison

/-!
# Functions and trace on actual affine spectra

A finite faithfully flat algebra with the canonical two-copy
comparison is a quotient on prime spectra. The topological trace
therefore has its exact kernel on every such affine spectrum.
-/

namespace ManuscriptAudit.CertifiedTorsorSpectrumTrace

open Topology PrimeSpectrum InvolutionTensorComparison
open DoubleCoverTopologicalTrace

noncomputable section

universe u v

variable (A E : Type u) [CommRing A] [CommRing E] [Algebra A E]

def projection : C(PrimeSpectrum E, PrimeSpectrum A) :=
  ⟨comap (algebraMap A E), continuous_comap _⟩

def spectrumSwap (σ : E ≃ₐ[A] E) : C(PrimeSpectrum E, PrimeSpectrum E) :=
  ⟨comap σ.toRingHom, continuous_comap _⟩

theorem quotient_projection (hfin : Module.Finite A E) (hfaith : Module.FaithfullyFlat A E) :
    IsQuotientMap (projection A E) := by
  letI : Module.Finite A E := hfin
  letI : Module.FaithfullyFlat A E := hfaith
  have hIntegr : (algebraMap A E).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  exact (PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hIntegr).isQuotientMap
    (continuous_comap _) PrimeSpectrum.comap_surjective_of_faithfullyFlat

theorem swap_involutive (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ) :
    Function.Involutive (spectrumSwap A E σ) := by
  intro p
  change comap σ.toRingHom (comap σ.toRingHom p) = p
  rw [← comap_comp_apply]
  have he : σ.toRingHom.comp σ.toRingHom = RingHom.id E := RingHom.ext hσ
  rw [he] <;> rfl

theorem projection_swap (σ : E ≃ₐ[A] E) (p : PrimeSpectrum E) :
    projection A E (spectrumSwap A E σ p) = projection A E p := by
  change comap (algebraMap A E) (comap σ.toRingHom p) = comap (algebraMap A E) p
  rw [← comap_comp_apply]
  have he : σ.toRingHom.comp (algebraMap A E) = algebraMap A E := RingHom.ext σ.commutes
  rw [he]

theorem swap_fiber_orbit (σ : E ≃ₐ[A] E) (c : CertifiedComparison A E σ)
    (p q : PrimeSpectrum E) (h : projection A E q = projection A E p) :
    q = p ∨ q = spectrumSwap A E σ p :=
  InvolutionSpectrumOrbits.spectrum_fiber_orbit A E σ c.equiv c.on_tmul p q h.symm

variable {M : Type v} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

def spectrumTrace (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (c : CertifiedComparison A E σ) (hfin : Module.Finite A E)
    (hfaith : Module.FaithfullyFlat A E) :
    C(PrimeSpectrum E, M) →+ C(PrimeSpectrum A, M) :=
  trace (projection A E) (spectrumSwap A E σ) (quotient_projection A E hfin hfaith)
    (swap_involutive A E σ hσ) (swap_fiber_orbit A E σ c)

theorem spectrumTrace_apply (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (c : CertifiedComparison A E σ) (hfin : Module.Finite A E)
    (hfaith : Module.FaithfullyFlat A E) (s : C(PrimeSpectrum E, M)) (p : PrimeSpectrum E) :
    spectrumTrace A E σ hσ c hfin hfaith s (projection A E p) =
      s p + s (spectrumSwap A E σ p) :=
  trace_apply _ _ _ _ _ s p

theorem spectrumTrace_kernel (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (c : CertifiedComparison A E σ) (hfin : Module.Finite A E)
    (hfaith : Module.FaithfullyFlat A E) (htwo : ∀ m : M, m + m = 0)
    (s : C(PrimeSpectrum E, M)) :
    spectrumTrace A E σ hσ c hfin hfaith s = 0 ↔
      ∃ t : C(PrimeSpectrum A, M), t.comp (projection A E) = s :=
  trace_eq_zero_iff_descends _ _ _ _ _ (projection_swap A E σ) htwo s

theorem spectrumTrace_zero_of_connected [PreconnectedSpace (PrimeSpectrum E)]
    [TotallyDisconnectedSpace M] (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (c : CertifiedComparison A E σ) (hfin : Module.Finite A E)
    (hfaith : Module.FaithfullyFlat A E) (htwo : ∀ m : M, m + m = 0)
    (s : C(PrimeSpectrum E, M)) :
    spectrumTrace A E σ hσ c hfin hfaith s = 0 :=
  trace_zero_of_connected _ _ _ _ _ htwo s

def spectrumMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    C(PrimeSpectrum S, PrimeSpectrum R) :=
  ⟨comap f, continuous_comap f⟩

variable {A' E' : Type u} [CommRing A'] [CommRing E'] [Algebra A' E']

theorem spectrumTrace_natural (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (c : CertifiedComparison A E σ) (hfin : Module.Finite A E)
    (hfaith : Module.FaithfullyFlat A E)
    (σ' : E' ≃ₐ[A'] E') (hσ' : Function.Involutive σ')
    (c' : CertifiedComparison A' E' σ') (hfin' : Module.Finite A' E')
    (hfaith' : Module.FaithfullyFlat A' E')
    (a : A →+* A') (b : E →+* E')
    (hBase : b.comp (algebraMap A E) = (algebraMap A' E').comp a)
    (hDeck : σ'.toRingHom.comp b = b.comp σ.toRingHom)
    (s : C(PrimeSpectrum E, M)) :
    spectrumTrace A' E' σ' hσ' c' hfin' hfaith' (s.comp (spectrumMap b)) =
      (spectrumTrace A E σ hσ c hfin hfaith s).comp (spectrumMap a) := by
  apply trace_natural
  · intro p
    change comap (algebraMap A E) (comap b p) = comap a (comap (algebraMap A' E') p)
    rw [← comap_comp_apply, ← comap_comp_apply, hBase]
  · intro p
    change comap b (comap σ'.toRingHom p) = comap σ.toRingHom (comap b p)
    rw [← comap_comp_apply, ← comap_comp_apply, hDeck]

end

end ManuscriptAudit.CertifiedTorsorSpectrumTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.CertifiedTorsorSpectrumTrace.quotient_projection,
        ``ManuscriptAudit.CertifiedTorsorSpectrumTrace.spectrumTrace_apply,
        ``ManuscriptAudit.CertifiedTorsorSpectrumTrace.spectrumTrace_kernel,
        ``ManuscriptAudit.CertifiedTorsorSpectrumTrace.spectrumTrace_natural,
        ``ManuscriptAudit.CertifiedTorsorSpectrumTrace.spectrumTrace_zero_of_connected] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
