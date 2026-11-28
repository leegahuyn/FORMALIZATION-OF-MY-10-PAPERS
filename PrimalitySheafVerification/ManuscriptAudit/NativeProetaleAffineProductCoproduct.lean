import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import PrimalitySheafVerification.ManuscriptAudit.FiniteProductSpectrumOpen
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCoproduct
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! The scheme of the literal finite product of chart rings is the
actual affine coproduct, preserving its actual component arrows. -/

namespace ManuscriptAudit.NativeProetaleAffineProductCoproduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap specMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]

private abbrev X (i : ι) := ProetaleAffineTensor.spectrum (B i)
private abbrev P := ProetaleAffineTensor.spectrum (∀ i, B i)

/-- The actual geometric coproduct map is given by the ring projections. -/
def comparison : (∐ X B) ⟶ P B := Sigma.desc (FiniteProductSpectrumOpen.projection B)

private theorem point_component (x : ↥(Limits.sigmaObj (X B))) :
    ∃ (i : ι) (y : ↥(X B i)), Sigma.ι (X B) i y = x := by
  let O := sigmaOpenCover (X B)
  obtain ⟨y, hy⟩ := O.covers x
  exact ⟨O.idx x, y, hy⟩

private theorem component_comp (i : ι) :
    Sigma.ι (X B) i ≫ comparison B = FiniteProductSpectrumOpen.projection B i :=
  Sigma.ι_desc _ _

set_option maxHeartbeats 3900000 in
/-- The actual coproduct-to-product-spectrum map is an isomorphism. -/
theorem comparison_isIso : IsIso (comparison B) := by
  have hInj : Function.Injective (comparison B) := by
    intro x y hxy
    obtain ⟨i, a, rfl⟩ := point_component B x
    obtain ⟨j, b, rfl⟩ := point_component B y
    have h := hxy
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, component_comp, component_comp] at h
    have h' : (PrimeSpectrum.sigmaToPiHomeo B) ⟨i, a⟩ =
        (PrimeSpectrum.sigmaToPiHomeo B) ⟨j, b⟩ := by
      rw [PrimeSpectrum.sigmaToPiHomeo_apply, PrimeSpectrum.sigmaToPi_apply,
        PrimeSpectrum.sigmaToPiHomeo_apply, PrimeSpectrum.sigmaToPi_apply]
      exact h
    have hSigma := (PrimeSpectrum.sigmaToPiHomeo B).injective h'
    exact congrArg (fun z : Σ i, PrimeSpectrum (B i) ↦ Sigma.ι (X B) z.1 z.2) hSigma
  have hSurj : Surjective (comparison B) := ⟨fun p ↦ by
    obtain ⟨i, x, hx⟩ := FiniteProductSpectrumOpen.exists_component B p
    refine ⟨Sigma.ι (X B) i x, ?_⟩
    rw [← Scheme.Hom.comp_apply, component_comp]
    exact hx⟩
  have hOpen : IsOpenImmersion (comparison B) := by
    apply IsOpenImmersion.of_forall_source_exists (comparison B) hInj
    intro x
    obtain ⟨i, y, hy⟩ := point_component B x
    let O := sigmaOpenCover (X B)
    letI : IsOpenImmersion (Sigma.ι (X B) i) := inferInstanceAs (IsOpenImmersion (O.f i))
    refine ⟨_, Sigma.ι (X B) i, inferInstance, Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩, ?_⟩
    rw [component_comp]
    exact FiniteProductSpectrumOpen.projection_isOpenImmersion B i
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hOpen, hSurj⟩

variable {A : Type u} [CommRing A] [∀ i, Algebra A (B i)]
  [∀ i, WeaklyEtale (structureMap A (B i))]

private abbrev coproductStructure :=
  Sigma.desc (fun i ↦ structureMap A (B i))

private theorem comparison_structure :
    comparison B ≫ structureMap A (∀ i, B i) = coproductStructure (A := A) B := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, component_comp, Sigma.ι_desc]
  exact ProetaleAffineTensor.specMap_structureMap A (Pi.evalAlgHom A B i)

set_option maxHeartbeats 3000000 in
/-- Finite products of the actual affine chart rings are themselves
actual weakly étale chart rings. -/
theorem product_weaklyEtale : WeaklyEtale (structureMap A (∀ i, B i)) := by
  let h := coproductStructure (A := A) B
  letI : WeaklyEtale h := IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale)
    (fun i ↦ inferInstanceAs (WeaklyEtale (structureMap A (B i))))
  letI : IsIso (comparison B) := comparison_isIso B
  let j := asIso (comparison B)
  have hf : j.inv ≫ h = structureMap A (∀ i, B i) := by
    change j.inv ≫ coproductStructure (A := A) B = _
    rw [← comparison_structure (A := A) B]
    change j.inv ≫ j.hom ≫ structureMap A (∀ i, B i) = _
    exact j.inv_hom_id_assoc _
  rw [← hf]
  infer_instance

end
end ManuscriptAudit.NativeProetaleAffineProductCoproduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeProetaleAffineProductCoproduct.comparison_isIso,
      ``ManuscriptAudit.NativeProetaleAffineProductCoproduct.product_weaklyEtale] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
