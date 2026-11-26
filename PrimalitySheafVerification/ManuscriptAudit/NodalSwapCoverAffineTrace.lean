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

theorem cover_faithfullyFlat (h2 : (2 : K) ≠ 0) : Module.FaithfullyFlat (A K) (E K) := by
  letI : Algebra.Etale (A K) (E K) := (cover_finite_etale K h2).2
  exact Module.FaithfullyFlat.of_comap_surjective (cover_spec_surjective K h2)

section ScalarExtension

variable (R : Type u) [CommRing R] [Algebra (A K) R]

abbrev coverOver := R ⊗[A K] E K

abbrev coverOverSwap :=
  InvolutionTensorBaseChange.baseSwap (A K) (E K) R (swap K)

set_option maxHeartbeats 900000 in
def coverOverCertificate (h2 : (2 : K) ≠ 0) :=
  @CertifiedTorsorBaseChange.liftCertified (A K) (E K) R
    (coordinates K).toCommRing (crossedPairs K).toCommRing inferInstance
    (crossedPairs K).algebra inferInstance (swap K) (NodalSwapCoverTorsor.certificate K h2)

private theorem coverOver_finite (h2 : (2 : K) ≠ 0) : Module.Finite R (coverOver K R) := by
  letI : Module.Finite (A K) (E K) := (cover_finite_etale K h2).1
  infer_instance

private theorem coverOver_faithfullyFlat (h2 : (2 : K) ≠ 0) :
    Module.FaithfullyFlat R (coverOver K R) := by
  letI : Module.FaithfullyFlat (A K) (E K) := cover_faithfullyFlat K h2
  infer_instance

variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

set_option maxHeartbeats 900000 in
def affineTrace (h2 : (2 : K) ≠ 0) :=
  spectrumTrace R (coverOver K R) (M := M) (coverOverSwap K R)
    (InvolutionTensorBaseChange.baseSwap_involutive (A K) (E K) R (swap K) (swap_twice K))
    (coverOverCertificate K R h2) (coverOver_finite K R h2) (coverOver_faithfullyFlat K R h2)

set_option maxHeartbeats 950000 in
theorem affineTrace_kernel (h2 : (2 : K) ≠ 0) (htwo : ∀ m : M, m + m = 0)
    (s : C(PrimeSpectrum (coverOver K R), M)) :
    affineTrace K R M h2 s = 0 ↔
      ∃ t : C(PrimeSpectrum R, M), t.comp (projection R (coverOver K R)) = s :=
  spectrumTrace_kernel R (coverOver K R) (coverOverSwap K R)
    (InvolutionTensorBaseChange.baseSwap_involutive (A K) (E K) R (swap K) (swap_twice K))
    (coverOverCertificate K R h2) (coverOver_finite K R h2) (coverOver_faithfullyFlat K R h2)
    htwo s

end ScalarExtension

section Global

variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

set_option maxHeartbeats 950000 in
def globalTrace (h2 : (2 : K) ≠ 0) :=
  spectrumTrace (A K) (E K) (M := M) (swap K) (swap_twice K)
    (NodalSwapCoverTorsor.certificate K h2) (cover_finite_etale K h2).1 (cover_faithfullyFlat K h2)

set_option maxHeartbeats 950000 in
theorem globalTrace_eq_zero (h2 : (2 : K) ≠ 0) [TotallyDisconnectedSpace M]
    (htwo : ∀ m : M, m + m = 0) (s : C(PrimeSpectrum (E K), M)) :
    globalTrace K M h2 s = 0 := by
  letI : ConnectedSpace (PrimeSpectrum (E K)) :=
    NodalSwapCoverConnected.connected_spectrum K h2
  exact spectrumTrace_zero_of_connected (A K) (E K) (swap K) (swap_twice K)
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
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.globalTrace_eq_zero,
        ``ManuscriptAudit.NodalSwapCoverAffineTrace.global_one_has_no_trace_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
