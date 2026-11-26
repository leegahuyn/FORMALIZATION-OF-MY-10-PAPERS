import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Fiber orbits from the canonical two-copy tensor comparison

The actual affine scheme pullback and its carrier identify each point
of the double overlap with one of the two graph maps.
-/

namespace ManuscriptAudit.InvolutionSpectrumOrbits

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PrimeSpectrum
open scoped TensorProduct

noncomputable section

private theorem prime_of_product {E : Type*} [CommRing E] (z : PrimeSpectrum (E × E)) :
    (∃ r : PrimeSpectrum E, comap (RingHom.fst E E) r = z) ∨
      ∃ r : PrimeSpectrum E, comap (RingHom.snd E E) r = z := by
  have hzero : ((1, 0) : E × E) * (0, 1) ∈ z.asIdeal := by
    have he : ((1, 0) : E × E) * (0, 1) = 0 := Prod.ext (by simp) (by simp)
    rw [he]
    exact z.asIdeal.zero_mem
  rcases z.isPrime.mem_or_mem hzero with hLeft | hRight
  · right
    have hh : z ∈ zeroLocus (RingHom.ker (RingHom.snd E E) : Set (E × E)) := by
      change RingHom.ker (RingHom.snd E E) ≤ z.asIdeal
      intro a ha
      change a.2 = 0 at ha
      have he : a * (1, 0) = a := Prod.ext (by simp) (by simp [ha])
      simpa only [he] using z.asIdeal.mul_mem_left a hLeft
    rw [← range_comap_of_surjective E (RingHom.snd E E) (fun a => ⟨(0, a), rfl⟩)] at hh
    exact hh
  · left
    have hh : z ∈ zeroLocus (RingHom.ker (RingHom.fst E E) : Set (E × E)) := by
      change RingHom.ker (RingHom.fst E E) ≤ z.asIdeal
      intro a ha
      change a.1 = 0 at ha
      have he : a * (0, 1) = a := Prod.ext (by simp [ha]) (by simp)
      simpa only [he] using z.asIdeal.mul_mem_left a hRight
    rw [← range_comap_of_surjective E (RingHom.fst E E) (fun a => ⟨(a, 0), rfl⟩)] at hh
    exact hh

universe u

variable (A E : Type u) [CommRing A] [CommRing E] [Algebra A E]

private abbrev T := E ⊗[A] E
private abbrev left : E →+* T A E :=
  (Algebra.TensorProduct.includeLeft : E →ₐ[A] T A E).toRingHom
private abbrev right : E →+* T A E :=
  (Algebra.TensorProduct.includeRight : E →ₐ[A] T A E).toRingHom

private theorem exists_double_overlap (p q : PrimeSpectrum E)
    (hpq : comap (algebraMap A E) p = comap (algebraMap A E) q) :
    ∃ z : PrimeSpectrum (T A E), comap (left A E) z = p ∧ comap (right A E) z = q := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A E))
  let f₁ := Spec.map (CommRingCat.ofHom (left A E))
  let f₂ := Spec.map (CommRingCat.ofHom (right A E))
  have hpull : IsPullback f₁ f₂ f f :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      ⟨⟨(CommRingCat.pushoutCocone A E E).condition⟩,
        ⟨CommRingCat.pushoutCoconeIsColimit A E E⟩⟩
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) p q hpq
  refine ⟨hpull.isoPullback.inv w, ?_, ?_⟩
  · change f₁ (hpull.isoPullback.inv w) = p
    rw [← Scheme.Hom.comp_apply, hpull.isoPullback_inv_fst]
    exact hw₁
  · change f₂ (hpull.isoPullback.inv w) = q
    rw [← Scheme.Hom.comp_apply, hpull.isoPullback_inv_snd]
    exact hw₂

set_option maxHeartbeats 1200000 in
/-- Under the canonical two-copy comparison, every spectrum fiber is one swap orbit. -/
theorem spectrum_fiber_orbit (σ : E ≃ₐ[A] E) (e : T A E ≃ₐ[E] (E × E))
    (he : ∀ a b : E, e (a ⊗ₜ[A] b) = (a * b, a * σ b))
    (p q : PrimeSpectrum E) (hpq : comap (algebraMap A E) p = comap (algebraMap A E) q) :
    q = p ∨ q = comap σ.toRingHom p := by
  obtain ⟨z, hz₁, hz₂⟩ := exists_double_overlap A E p q hpq
  let z' := (PrimeSpectrum.comapEquiv e.toRingEquiv) z
  have hz : comap e.toRingHom z' = z :=
    (PrimeSpectrum.comapEquiv e.toRingEquiv).symm_apply_apply z
  have hL₁ : (RingHom.fst E E).comp (e.toRingHom.comp (left A E)) = RingHom.id E := by
    ext a
    change (e (a ⊗ₜ[A] (1 : E))).1 = a
    rw [he, mul_one]
  have hL₂ : (RingHom.snd E E).comp (e.toRingHom.comp (left A E)) = RingHom.id E := by
    ext a
    change (e (a ⊗ₜ[A] (1 : E))).2 = a
    rw [he, map_one, mul_one]
  have hR₁ : (RingHom.fst E E).comp (e.toRingHom.comp (right A E)) = RingHom.id E := by
    ext b
    change (e ((1 : E) ⊗ₜ[A] b)).1 = b
    rw [he, one_mul]
  have hR₂ : (RingHom.snd E E).comp (e.toRingHom.comp (right A E)) = σ.toRingHom := by
    ext b
    change (e ((1 : E) ⊗ₜ[A] b)).2 = σ b
    rw [he, one_mul]
  rcases prime_of_product z' with ⟨r, hr⟩ | ⟨r, hr⟩
  · left
    rw [← hz, ← hr, ← comap_comp_apply, ← comap_comp_apply, hL₁] at hz₁
    rw [← hz, ← hr, ← comap_comp_apply, ← comap_comp_apply, hR₁] at hz₂
    exact hz₂.symm.trans hz₁
  · right
    rw [← hz, ← hr, ← comap_comp_apply, ← comap_comp_apply, hL₂] at hz₁
    rw [← hz, ← hr, ← comap_comp_apply, ← comap_comp_apply, hR₂] at hz₂
    rw [← hz₁]
    exact hz₂.symm

end

end ManuscriptAudit.InvolutionSpectrumOrbits

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.InvolutionSpectrumOrbits.spectrum_fiber_orbit
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
