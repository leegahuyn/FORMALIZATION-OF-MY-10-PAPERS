import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! An arbitrary intersection of clopen basic opens of an affine scheme is
the exact image of a weakly étale affine localization chart. -/

namespace ManuscriptAudit.AffineClopenIntersectionChart

open AlgebraicGeometry CategoryTheory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {I : Type*} (e : I → R)

abbrev denominators : Submonoid R := Submonoid.closure (Set.range e)

abbrev chartRing := Localization (denominators e)

abbrev chartMap : Spec (CommRingCat.of (chartRing e)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (chartRing e)))

/-- Exact range of the localization of the actual affine scheme. -/
theorem chart_range :
    Set.range (chartMap e) = {x | ∀ i, x ∈ (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum R))} := by
  change Set.range (PrimeSpectrum.comap (algebraMap R (chartRing e))) = _
  rw [PrimeSpectrum.localization_comap_range (chartRing e) (denominators e)]
  ext x
  constructor
  · intro h i
    exact fun hmem ↦ Set.disjoint_left.mp h (Submonoid.subset_closure ⟨i, rfl⟩) hmem
  · intro h
    letI : x.asIdeal.IsPrime := x.2
    have hle : denominators e ≤ x.asIdeal.primeCompl := by
      apply Submonoid.closure_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    exact Set.disjoint_left.mpr (fun _ hx hy ↦ hle hx hy)

private theorem elem_idempotent (he : ∀ i, IsIdempotentElem (e i)) (a : denominators e) :
    IsIdempotentElem (a : R) := by
  obtain ⟨a, ha⟩ := a
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact he i
  | one => exact IsIdempotentElem.one
  | mul x y hx hy hxi hyi => exact hxi.mul hyi

private theorem algebraMap_surjective (he : ∀ i, IsIdempotentElem (e i)) :
    Function.Surjective (algebraMap R (chartRing e)) := by
  intro z
  obtain ⟨⟨a, b⟩, hz⟩ := IsLocalization.surj (denominators e) z
  have hb : algebraMap R (chartRing e) b = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units (chartRing e) b)).mp
      ((elem_idempotent e he b).map (algebraMap R (chartRing e)))
  exact ⟨a, by simpa only [hb, mul_one] using hz.symm⟩

/-- The simultaneous clopen slice is weakly étale even for an infinite family. -/
theorem chart_weaklyEtale (he : ∀ i, IsIdempotentElem (e i)) : WeaklyEtale (chartMap e) := by
  letI : Module.Flat R (chartRing e) := inferInstance
  letI : Flat (chartMap e) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : IsClosedImmersion (chartMap e) :=
    IsClosedImmersion.spec_of_surjective _ (algebraMap_surjective e he)
  exact ⟨inferInstance, inferInstance⟩

end

end ManuscriptAudit.AffineClopenIntersectionChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineClopenIntersectionChart.chart_range,
      ``ManuscriptAudit.AffineClopenIntersectionChart.chart_weaklyEtale] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
