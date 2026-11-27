import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleRadicialIso

/-! A weakly étale affine morphism is formally unramified. The equalizer of
two lifts comes from the flat diagonal, and a nilpotent thickening makes that
equalizer surjective. -/

namespace ManuscriptAudit.WeaklyEtaleAffineUnramified

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private abbrev structureMap := Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- Formal unramifiedness of the actual affine weakly étale algebra. -/
theorem formallyUnramified [WeaklyEtale (structureMap R S)] :
    Algebra.FormallyUnramified R S := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro T _ _ I hI a b e
  let f := structureMap R S
  let u := Spec.map (CommRingCat.ofHom a.toRingHom)
  let v := Spec.map (CommRingCat.ofHom b.toRingHom)
  have hu : u ≫ f = v ≫ f := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (a.commutes x).trans (b.commutes x).symm
  let w := pullback.lift u v hu
  let d := pullback.diagonal f
  let g := pullback.fst w d
  let n := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hn : I ≤ nilradical T := by
    intro x hx
    refine ⟨2, ?_⟩
    have ht : x ^ 2 ∈ I ^ 2 := by
      simpa only [pow_two] using (Ideal.mul_mem_mul hx hx : x * x ∈ I * I)
    simpa only [hI, Ideal.mem_bot] using ht
  letI : Surjective n := ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hn).surjective⟩
  have hab : n ≫ u = n ≫ v := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact DFunLike.congr_fun e x
  have hwu : w ≫ pullback.fst f f = u := pullback.lift_fst u v hu
  have hwv : w ≫ pullback.snd f f = v := pullback.lift_snd u v hu
  have hdu : d ≫ pullback.fst f f = 𝟙 _ := pullback.diagonal_fst f
  have hdv : d ≫ pullback.snd f f = 𝟙 _ := pullback.diagonal_snd f
  have hw : n ≫ w = (n ≫ u) ≫ d := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hwu, hdu, Category.comp_id]
    · simp only [Category.assoc, hwv, hdv, Category.comp_id, hab]
  let t := pullback.lift n (n ≫ u) hw
  have ht : t ≫ g = n := pullback.lift_fst n (n ≫ u) hw
  letI : Surjective g := ⟨fun y ↦ by
    obtain ⟨z, hz⟩ := n.surjective y
    exact ⟨t z, (congrArg (fun r ↦ r z) ht).trans hz⟩⟩
  letI : Flat d := inferInstanceAs (Flat (pullback.diagonal f))
  letI : IsClosedImmersion d := inferInstanceAs (IsClosedImmersion (pullback.diagonal f))
  letI : Flat g := inferInstanceAs (Flat (pullback.fst w d))
  letI : IsClosedImmersion g := inferInstanceAs (IsClosedImmersion (pullback.fst w d))
  letI : IsIso g := WeaklyEtaleRadicialIso.isIso_of_flat_surjective_qc_mono g
  have uv : u = v := by
    apply (cancel_epi g).mp
    calc
      g ≫ u = (g ≫ w) ≫ pullback.fst f f := by rw [Category.assoc, hwu]
      _ = (g ≫ w) ≫ pullback.snd f f := by
        change (pullback.fst w d ≫ w) ≫ _ = (pullback.fst w d ≫ w) ≫ _
        rw [pullback.condition]
        simp only [Category.assoc, hdu, hdv]
      _ = g ≫ v := by rw [Category.assoc, hwv]
  have hh := congrArg Spec.preimage uv
  simp only [u, v, Spec.preimage_map] at hh
  apply AlgHom.ext
  intro x
  exact congrArg (fun h ↦ h.hom x) hh

end
end ManuscriptAudit.WeaklyEtaleAffineUnramified

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineUnramified.formallyUnramified
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
