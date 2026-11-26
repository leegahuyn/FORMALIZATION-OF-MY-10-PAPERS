import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSquare
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCover

/-!
# The spectrum of the crossed algebra is connected

The two normalization lines have intersecting images. The zero
products between the two projection kernels ensure that these two
images cover the entire spectrum.
-/

namespace ManuscriptAudit.NodalSwapCoverConnected

open NodalSwapCover NodalConductorSquare Polynomial PrimeSpectrum

universe u

variable (K : Type u) [Field K]

def firstProjection : Cover K →+* K[X] where
  toFun z := z.val.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def secondProjection : Cover K →+* K[X] :=
  (firstProjection K).comp (swap K).toRingHom

theorem firstProjection_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (firstProjection K) := by
  intro f
  obtain ⟨g, hg⟩ := branches_surjective K h2 (f.eval (-1), f.eval 1)
  change (g.eval 1, g.eval (-1)) = (f.eval (-1), f.eval 1) at hg
  exact ⟨⟨(f, g), (congrArg Prod.snd hg).symm, (congrArg Prod.fst hg).symm⟩, rfl⟩

theorem secondProjection_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (secondProjection K) :=
  (firstProjection_surjective K h2).comp (swap K).surjective

private theorem mem_comap_range_of_ker_le {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (p : PrimeSpectrum R)
    (h : RingHom.ker f ≤ p.asIdeal) : p ∈ Set.range (comap f) := by
  rw [range_comap_of_surjective S f hf]
  exact h

set_option maxHeartbeats 1500000 in
private theorem images_cover (h2 : (2 : K) ≠ 0) :
    Set.range (comap (firstProjection K)) ∪ Set.range (comap (secondProjection K)) =
      (Set.univ : Set (PrimeSpectrum (Cover K))) := by
  apply Set.eq_univ_of_forall
  intro p
  by_cases hf : RingHom.ker (firstProjection K) ≤ p.asIdeal
  · exact Or.inl (mem_comap_range_of_ker_le (firstProjection K) (firstProjection_surjective K h2) p hf)
  · apply Or.inr
    apply mem_comap_range_of_ker_le (secondProjection K) (secondProjection_surjective K h2) p
    intro b hb
    by_contra hn
    apply hf
    intro a ha
    have hzero : a * b = 0 := by
      change a.val.1 = 0 at ha
      change b.val.2 = 0 at hb
      apply Subtype.ext
      exact Prod.ext (by change a.val.1 * b.val.1 = 0; rw [ha, zero_mul])
        (by change a.val.2 * b.val.2 = 0; rw [hb, mul_zero])
    have hm : a * b ∈ p.asIdeal := hzero.symm ▸ p.asIdeal.zero_mem
    exact (p.isPrime.mem_or_mem hm).resolve_right hn

private theorem images_meet :
    (Set.range (comap (firstProjection K)) ∩ Set.range (comap (secondProjection K))).Nonempty := by
  let p := comap (evalRingHom (1 : K)) (⊥ : PrimeSpectrum K)
  let q := comap (evalRingHom (-1 : K)) (⊥ : PrimeSpectrum K)
  have h : comap (firstProjection K) p = comap (secondProjection K) q := by
    apply PrimeSpectrum.ext
    ext z
    change z.val.1.eval 1 ∈ (⊥ : Ideal K) ↔ z.val.2.eval (-1) ∈ (⊥ : Ideal K)
    rw [(condition K z).1]
  exact ⟨_, ⟨p, rfl⟩, ⟨q, h.symm⟩⟩

/-- The actual affine spectrum of the crossed algebra is connected. -/
theorem connected_spectrum (h2 : (2 : K) ≠ 0) :
    ConnectedSpace (PrimeSpectrum (Cover K)) := by
  rw [connectedSpace_iff_univ, ← images_cover K h2]
  exact IsConnected.union (images_meet K)
    (isConnected_range (continuous_comap (firstProjection K)))
    (isConnected_range (continuous_comap (secondProjection K)))

end ManuscriptAudit.NodalSwapCoverConnected

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCoverConnected.firstProjection_surjective,
        ``ManuscriptAudit.NodalSwapCoverConnected.connected_spectrum] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
