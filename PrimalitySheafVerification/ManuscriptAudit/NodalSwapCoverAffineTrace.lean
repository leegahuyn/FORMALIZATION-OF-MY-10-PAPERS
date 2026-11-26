import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.CertifiedTorsorBaseChange
import PrimalitySheafVerification.ManuscriptAudit.CertifiedTorsorSpectrumTrace
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverConnected
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverEtale
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverTorsor

/-!
# Actual affine traces for the nodal cover

For any given affine base algebra the crossed cover supplies the
canonical spectrum trace and its exact kernel. At the actual node
the trace on global sections with two-torsion coefficients vanishes.
-/

namespace ManuscriptAudit.NodalSwapCoverAffineTrace

open NodalConductor NodalSwapCover NodalSwapCoverEtale
open CertifiedTorsorSpectrumTrace
open scoped TensorProduct

noncomputable section

universe u v

variable (K : Type u) [Field K]

private abbrev A : Type u := ↥(coordinates K)
private abbrev E : Type u := Cover K

private abbrev nodeSwap : E K ≃ₐ[A K] E K := swap K

private theorem nodeSwap_involutive : Function.Involutive (nodeSwap K) := swap_twice K

private theorem flatAfterBaseChange (A E R : Type u) [CommRing A] [CommRing E]
    [CommRing R] [Algebra A E] [Algebra A R] (h : Module.FaithfullyFlat A E) :
    Module.FaithfullyFlat R (R ⊗[A] E) := by
  letI := h
  infer_instance

theorem cover_faithfullyFlat (h2 : (2 : K) ≠ 0) : Module.FaithfullyFlat (A K) (E K) := by
  letI : Algebra.Etale (A K) (E K) := (cover_finite_etale K h2).2
  exact Module.FaithfullyFlat.of_comap_surjective (A := A K) (B := E K)
    (cover_spec_surjective K h2)

section ScalarExtension

variable (R : Type u) [CommRing R] [Algebra (A K) R]

abbrev coverOver := R ⊗[A K] E K

abbrev coverOverSwap :=
  @InvolutionTensorBaseChange.baseSwap (A K) (E K) R
    (coordinates K).toCommRing (crossedPairs K).toCommRing inferInstance
    (crossedPairs K).algebra inferInstance (nodeSwap K)

theorem coverOverSwap_involutive : Function.Involutive (coverOverSwap K R) :=
  @InvolutionTensorBaseChange.baseSwap_involutive (A K) (E K) R
    (coordinates K).toCommRing (crossedPairs K).toCommRing inferInstance
    (crossedPairs K).algebra inferInstance (nodeSwap K) (nodeSwap_involutive K)

set_option maxHeartbeats 900000 in
def coverOverCertificate (h2 : (2 : K) ≠ 0) :=
  @CertifiedTorsorBaseChange.liftCertified (A K) (E K) R
    (coordinates K).toCommRing (crossedPairs K).toCommRing inferInstance
    (crossedPairs K).algebra inferInstance (nodeSwap K) (NodalSwapCoverTorsor.certificate K h2)

theorem coverOver_finite (h2 : (2 : K) ≠ 0) : Module.Finite R (coverOver K R) := by
  letI : Module.Finite (A K) (E K) := (cover_finite_etale K h2).1
  infer_instance

theorem coverOver_faithfullyFlat (h2 : (2 : K) ≠ 0) :
    Module.FaithfullyFlat R (coverOver K R) :=
  @flatAfterBaseChange (A K) (E K) R
    (coordinates K).toCommRing (crossedPairs K).toCommRing inferInstance
    (crossedPairs K).algebra inferInstance (cover_faithfullyFlat K h2)

variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

set_option maxHeartbeats 900000 in
def affineTrace (h2 : (2 : K) ≠ 0) :=
  spectrumTrace R (coverOver K R) (M := M) (coverOverSwap K R)
    (coverOverSwap_involutive K R)
    (coverOverCertificate K R h2) (coverOver_finite K R h2) (coverOver_faithfullyFlat K R h2)

set_option maxHeartbeats 950000 in
theorem affineTrace_kernel (h2 : (2 : K) ≠ 0) (htwo : ∀ m : M, m + m = 0)
    (s : C(PrimeSpectrum (coverOver K R), M)) :
    affineTrace K R M h2 s = 0 ↔
      ∃ t : C(PrimeSpectrum R, M), t.comp (projection R (coverOver K R)) = s :=
  spectrumTrace_kernel R (coverOver K R) (M := M) (coverOverSwap K R)
    (coverOverSwap_involutive K R)
    (coverOverCertificate K R h2) (coverOver_finite K R h2) (coverOver_faithfullyFlat K R h2)
    htwo s

set_option maxHeartbeats 950000 in
theorem affineTrace_eq_zero_of_connected (h2 : (2 : K) ≠ 0)
    [PreconnectedSpace (PrimeSpectrum (coverOver K R))] [TotallyDisconnectedSpace M]
    (htwo : ∀ m : M, m + m = 0) (s : C(PrimeSpectrum (coverOver K R), M)) :
    affineTrace K R M h2 s = 0 :=
  spectrumTrace_zero_of_connected R (coverOver K R) (M := M) (coverOverSwap K R)
    (coverOverSwap_involutive K R)
    (coverOverCertificate K R h2) (coverOver_finite K R h2) (coverOver_faithfullyFlat K R h2)
    htwo s

variable (S : Type u) [CommRing S] [Algebra (A K) S]

def coverOverMap (f : R →ₐ[A K] S) : coverOver K R →ₐ[A K] coverOver K S :=
  Algebra.TensorProduct.map f (AlgHom.id (A K) (E K))

private theorem coverOverMap_base (f : R →ₐ[A K] S) :
    (coverOverMap K R S f).toRingHom.comp (algebraMap R (coverOver K R)) =
      (algebraMap S (coverOver K S)).comp f.toRingHom := by
  apply RingHom.ext
  intro r
  change coverOverMap K R S f (r ⊗ₜ[A K] (1 : E K)) = f r ⊗ₜ[A K] (1 : E K)
  rw [coverOverMap, Algebra.TensorProduct.map_tmul] <;> rfl

private theorem coverOverMap_deck (f : R →ₐ[A K] S) :
    (coverOverSwap K S).toRingHom.comp (coverOverMap K R S f).toRingHom =
      (coverOverMap K R S f).toRingHom.comp (coverOverSwap K R).toRingHom := by
  apply RingHom.ext
  intro z
  change coverOverSwap K S (coverOverMap K R S f z) = coverOverMap K R S f (coverOverSwap K R z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [coverOverMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      InvolutionTensorBaseChange.baseSwap_tmul]
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option maxHeartbeats 1000000 in
theorem affineTrace_natural (h2 : (2 : K) ≠ 0) (f : R →ₐ[A K] S)
    (s : C(PrimeSpectrum (coverOver K R), M)) :
    affineTrace K S M h2 (s.comp (spectrumMap (coverOverMap K R S f).toRingHom)) =
      (affineTrace K R M h2 s).comp (spectrumMap f.toRingHom) :=
  spectrumTrace_natural R (coverOver K R) (M := M) (coverOverSwap K R)
    (coverOverSwap_involutive K R)
    (coverOverCertificate K R h2) (coverOver_finite K R h2) (coverOver_faithfullyFlat K R h2)
    (coverOverSwap K S)
    (coverOverSwap_involutive K S)
    (coverOverCertificate K S h2) (coverOver_finite K S h2) (coverOver_faithfullyFlat K S h2)
    f.toRingHom (coverOverMap K R S f).toRingHom (coverOverMap_base K R S f)
    (coverOverMap_deck K R S f) s

end ScalarExtension

section Global

variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

set_option maxHeartbeats 950000 in
def globalTrace (h2 : (2 : K) ≠ 0) :=
  spectrumTrace (A K) (E K) (M := M) (nodeSwap K) (nodeSwap_involutive K)
    (NodalSwapCoverTorsor.certificate K h2) (cover_finite_etale K h2).1 (cover_faithfullyFlat K h2)

set_option maxHeartbeats 950000 in
theorem globalTrace_eq_zero (h2 : (2 : K) ≠ 0) [TotallyDisconnectedSpace M]
    (htwo : ∀ m : M, m + m = 0) (s : C(PrimeSpectrum (E K), M)) :
    globalTrace K M h2 s = 0 := by
  letI : ConnectedSpace (PrimeSpectrum (E K)) :=
    NodalSwapCoverConnected.connected_spectrum K h2
  exact spectrumTrace_zero_of_connected (A K) (E K) (M := M) (nodeSwap K) (nodeSwap_involutive K)
    (NodalSwapCoverTorsor.certificate K h2) (cover_finite_etale K h2).1 (cover_faithfullyFlat K h2)
    htwo s

end Global

section Two

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

/-- The constant section 1 is outside the image of the actual global trace. -/
theorem global_one_has_no_trace_lift (h2 : (2 : K) ≠ 0) :
    ¬ ∃ s : C(PrimeSpectrum (E K), ZMod 2),
      globalTrace K (ZMod 2) h2 s = ContinuousMap.const (PrimeSpectrum (A K)) 1 := by
  rintro ⟨s, hs⟩
  have htwo (m : ZMod 2) : m + m = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [globalTrace_eq_zero K (ZMod 2) h2 htwo s] at hs
  have h01 : (0 : ZMod 2) = 1 := congrArg
    (fun f : C(PrimeSpectrum (A K), ZMod 2) => f (⊥ : PrimeSpectrum (A K))) hs
  exact zero_ne_one h01

end Two

end

end ManuscriptAudit.NodalSwapCoverAffineTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCoverAffineTrace.cover_faithfullyFlat,
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.coverOverCertificate,
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.affineTrace_kernel,
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.affineTrace_eq_zero_of_connected,
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.affineTrace_natural,
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.globalTrace_eq_zero,
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.global_one_has_no_trace_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
