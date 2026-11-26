import Lean.Util.CollectAxioms
import Mathlib.Topology.Piecewise
import PrimalitySheafVerification.ManuscriptAudit.CertifiedTorsorSpectrumTrace

/-!
# A split trace lifts every section

Complementary idempotents exchanged by the involution give clopen
halves. Extending a section by zero on one half lifts it through trace.
-/

namespace ManuscriptAudit.CertifiedTorsorSpectrumTrace

open Topology PrimeSpectrum InvolutionTensorComparison

noncomputable section

universe u v

variable (A E : Type u) [CommRing A] [CommRing E] [Algebra A E]
  {M : Type v} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

theorem spectrumTrace_surjective_of_idempotents (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (c : CertifiedComparison A E σ) (hfin : Module.Finite A E)
    (hfaith : Module.FaithfullyFlat A E)
    (e f : E) (hmul : e * f = 0) (hadd : e + f = 1) (hswap : σ e = f) :
    Function.Surjective (spectrumTrace A E (M := M) σ hσ c hfin hfaith) := by
  classical
  intro t
  let U : Set (PrimeSpectrum E) := basicOpen e
  have hU : IsClopen U := isClopen_basicOpen_of_mul_add e f hmul hadd
  have hcomp : (basicOpen f : Set (PrimeSpectrum E)) = Uᶜ := by
    change (basicOpen f : Set (PrimeSpectrum E)) = (basicOpen e : Set (PrimeSpectrum E))ᶜ
    rw [basicOpen_eq_zeroLocus_compl f, basicOpen_eq_zeroLocus_of_mul_add e f hmul hadd]
  have hs (p : PrimeSpectrum E) : spectrumSwap A E σ p ∈ U ↔ p ∉ U := by
    change σ e ∉ p.asIdeal ↔ p ∉ U
    rw [hswap]
    change p ∈ (basicOpen f : Set (PrimeSpectrum E)) ↔ p ∉ U
    rw [hcomp] <;> rfl
  let s : C(PrimeSpectrum E, M) :=
    ⟨U.piecewise (t ∘ projection A E) (fun _ => 0),
      (t.continuous.comp (projection A E).continuous).piecewise
        (by simp [hU.frontier_eq]) continuous_const⟩
  refine ⟨s, ContinuousMap.ext fun q => ?_⟩
  obtain ⟨p, rfl⟩ := (quotient_projection A E hfin hfaith).surjective q
  rw [spectrumTrace_apply]
  by_cases hp : p ∈ U
  · have hp' : spectrumSwap A E σ p ∉ U := fun h => (hs p).mp h hp
    simp [s, Set.piecewise, hp, hp']
  · have hp' : spectrumSwap A E σ p ∈ U := (hs p).mpr hp
    simp [s, Set.piecewise, hp, hp', projection_swap]

end

end ManuscriptAudit.CertifiedTorsorSpectrumTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CertifiedTorsorSpectrumTrace.spectrumTrace_surjective_of_idempotents
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
