import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SpectrumFiniteIdempotentPartition

/-! An injective ring map detects equality of actual finite-coefficient sections. -/

namespace ManuscriptAudit.SpectrumFiniteContinuousInjection

open PrimeSpectrum SpectrumFiniteIdempotentPartition

noncomputable section

variable {S R A : Type*} [CommRing S] [CommRing R]
  [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

/-- Equality of two finite discrete sections is detected by their literal pullbacks. -/
theorem pullback_injective (φ : S →+* R) (hφ : Function.Injective φ)
    {f g : PrimeSpectrum S → A} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f (PrimeSpectrum.comap φ x) = g (PrimeSpectrum.comap φ x)) :
    f = g := by
  obtain ⟨e, he, hfe⟩ := exists_idempotent_fibers f hf
  obtain ⟨d, hd, hgd⟩ := exists_idempotent_fibers g hg
  have heq (a : A) : e a = d a := by
    apply hφ
    apply basicOpen_injOn_isIdempotentElem ((he.idem a).map φ) ((hd.idem a).map φ)
    apply TopologicalSpace.Opens.ext
    intro x
    change PrimeSpectrum.comap φ x ∈ (basicOpen (e a) : Set (PrimeSpectrum S)) ↔
      PrimeSpectrum.comap φ x ∈ (basicOpen (d a) : Set (PrimeSpectrum S))
    rw [← hfe a, ← hgd a]
    change f (PrimeSpectrum.comap φ x) = a ↔ g (PrimeSpectrum.comap φ x) = a
    rw [h x]
  funext x
  have hx : x ∈ (basicOpen (e (f x)) : Set (PrimeSpectrum S)) := by
    rw [← hfe (f x)]
    exact Set.mem_singleton _
  rw [heq (f x), ← hgd (f x)] at hx
  exact (show g x = f x from hx).symm

end
end ManuscriptAudit.SpectrumFiniteContinuousInjection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SpectrumFiniteContinuousInjection.pullback_injective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
