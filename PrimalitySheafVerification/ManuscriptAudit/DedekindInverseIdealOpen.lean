import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import PrimalitySheafVerification.ManuscriptAudit.DedekindInverseIdealLocalization

/-! The genuine affine scheme of the inverse-ideal algebra is the
open complement of the support of a nonzero Dedekind ideal. -/

namespace ManuscriptAudit.DedekindInverseIdealOpen

open AlgebraicGeometry CategoryTheory
open DedekindInverseIdealAlgebra (outsideAlgebra map_eq_top)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (A K : Type u) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] (I : Ideal A)

private abbrev C := outsideAlgebra A K I
private abbrev X := Spec (CommRingCat.of (C A K I))
private abbrev Y := Spec (CommRingCat.of A)

/-- The affine stage's literal map to the original Dedekind scheme. -/
abbrev stageMap : X A K I ⟶ Y A :=
  Spec.map (CommRingCat.ofHom (algebraMap A (C A K I)))

private abbrev P (a : A) := Localization.Away (algebraMap A (C A K I) a)
private abbrev localMap (a : A) : Spec (CommRingCat.of (P A K I a)) ⟶ X A K I :=
  Spec.map (CommRingCat.ofHom (algebraMap (C A K I) (P A K I a)))

private theorem comp_eq (a : A) :
    localMap A K I a ≫ stageMap A K I =
      Spec.map (CommRingCat.ofHom (algebraMap A (P A K I a))) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq A (C A K I) (P A K I a)).symm

private theorem localMap_isOpenImmersion (a : A) : IsOpenImmersion (localMap A K I a) :=
  IsOpenImmersion.of_isLocalization (algebraMap A (C A K I) a)

private theorem localMap_range (a : A) :
    Set.range (localMap A K I a) =
      (PrimeSpectrum.basicOpen (algebraMap A (C A K I) a) : Set (PrimeSpectrum (C A K I))) :=
  PrimeSpectrum.localization_away_comap_range (P A K I a) (algebraMap A (C A K I) a)

private theorem comp_isOpenImmersion (hI : I ≠ ⊥) (a : A) (ha : a ∈ I) (h₀ : a ≠ 0) :
    IsOpenImmersion (localMap A K I a ≫ stageMap A K I) := by
  rw [comp_eq]
  letI := DedekindInverseIdealLocalization.isLocalization_away A K I hI ha h₀
  exact IsOpenImmersion.of_isLocalization a

private theorem comp_range (hI : I ≠ ⊥) (a : A) (ha : a ∈ I) (h₀ : a ≠ 0) :
    Set.range (localMap A K I a ≫ stageMap A K I) = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  rw [comp_eq]
  letI := DedekindInverseIdealLocalization.isLocalization_away A K I hI ha h₀
  exact PrimeSpectrum.localization_away_comap_range (P A K I a) a

private theorem exists_chart (hI : I ≠ ⊥) (x : X A K I) :
    ∃ a ∈ I, algebraMap A (C A K I) a ∉ x.asIdeal := by
  by_contra h
  have hLe : I ≤ x.asIdeal.comap (algebraMap A (C A K I)) := by
    intro a ha
    exact Classical.not_not.mp (fun hx ↦ h ⟨a, ha, hx⟩)
  have hLe' := Ideal.map_le_iff_le_comap.mpr hLe
  rw [map_eq_top A K I hI] at hLe'
  exact x.isPrime.ne_top (top_le_iff.mp hLe')

private theorem chart_nonzero {x : X A K I} {a : A}
    (ha : algebraMap A (C A K I) a ∉ x.asIdeal) : a ≠ 0 := by
  intro h
  apply ha
  rw [h, map_zero]
  exact x.asIdeal.zero_mem

private theorem chart_mem_range {x : X A K I} {a : A}
    (ha : algebraMap A (C A K I) a ∉ x.asIdeal) : x ∈ Set.range (localMap A K I a) := by
  rw [localMap_range]
  exact (PrimeSpectrum.mem_basicOpen _ x).mpr ha

set_option maxHeartbeats 2400000 in
/-- This actual affine stage is an open subscheme of the Dedekind spectrum. -/
theorem stageMap_isOpenImmersion (hI : I ≠ ⊥) : IsOpenImmersion (stageMap A K I) := by
  apply IsOpenImmersion.of_forall_source_exists (stageMap A K I)
  · intro x y hxy
    obtain ⟨a, ha, hx⟩ := exists_chart A K I hI x
    have hy : algebraMap A (C A K I) a ∉ y.asIdeal := by
      change a ∉ (stageMap A K I y).asIdeal
      rw [← hxy]
      exact hx
    obtain ⟨p, hp⟩ := chart_mem_range A K I hx
    obtain ⟨q, hq⟩ := chart_mem_range A K I hy
    letI := comp_isOpenImmersion A K I hI a ha (chart_nonzero A K I hx)
    have h : p = q := (localMap A K I a ≫ stageMap A K I).isOpenEmbedding.injective (by
      change stageMap A K I (localMap A K I a p) = stageMap A K I (localMap A K I a q)
      rw [hp, hq]
      exact hxy)
    exact hp.symm.trans ((congrArg (localMap A K I a) h).trans hq)
  · intro x
    obtain ⟨a, ha, hx⟩ := exists_chart A K I hI x
    letI := localMap_isOpenImmersion A K I a
    refine ⟨_, localMap A K I a, inferInstance, ?_,
      comp_isOpenImmersion A K I hI a ha (chart_nonzero A K I hx)⟩
    exact Scheme.Hom.mem_opensRange.mpr (chart_mem_range A K I hx)

set_option maxHeartbeats 1800000 in
/-- The image of the actual open immersion is exactly the desired open complement. -/
theorem stageMap_range (hI : I ≠ ⊥) :
    Set.range (stageMap A K I) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, ha, hx⟩ := exists_chart A K I hI x
    change ¬ ((I : Set A) ⊆ (stageMap A K I x).asIdeal)
    exact fun h ↦ hx (h ha)
  · intro hp
    change ¬ ((I : Set A) ⊆ p.asIdeal) at hp
    have h : ∃ a ∈ I, a ∉ p.asIdeal := by
      by_contra h
      exact hp (fun a ha ↦ Classical.not_not.mp (fun hpa ↦ h ⟨a, ha, hpa⟩))
    obtain ⟨a, ha, hpa⟩ := h
    have h₀ : a ≠ 0 := fun h ↦ hpa (h.symm ▸ p.asIdeal.zero_mem)
    have hMem : p ∈ Set.range (localMap A K I a ≫ stageMap A K I) := by
      rw [comp_range A K I hI a ha h₀]
      exact (PrimeSpectrum.mem_basicOpen a p).mpr hpa
    obtain ⟨x, hx⟩ := hMem
    exact ⟨localMap A K I a x, hx⟩

include K in
/-- Every nonempty open of the actual affine Dedekind spectrum is affine. -/
theorem isAffineOpen_of_ne_bot (U : (Y A).Opens) (hU : U ≠ ⊥) : IsAffineOpen U := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    ((U : Set (Y A))ᶜ)).mp U.isOpen.isClosed_compl
  have hJ₀ : J ≠ ⊥ := by
    intro h
    apply hU
    apply TopologicalSpace.Opens.ext
    have he : (U : Set (Y A))ᶜ = Set.univ := by simpa [h] using hJ
    change (U : Set (Y A)) = ∅
    calc
      _ = ((U : Set (Y A))ᶜ)ᶜ := (compl_compl _).symm
      _ = _ := by rw [he, Set.compl_univ]
  let f := stageMap A K J
  letI : IsOpenImmersion f := stageMap_isOpenImmersion A K J hJ₀
  have hEq : f.opensRange = U := by
    apply TopologicalSpace.Opens.ext
    change Set.range f = (U : Set (Y A))
    rw [stageMap_range A K J hJ₀, ← hJ, compl_compl]
  rw [← hEq]
  exact isAffineOpen_opensRange f

end
end ManuscriptAudit.DedekindInverseIdealOpen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindInverseIdealOpen.stageMap_isOpenImmersion,
      ``ManuscriptAudit.DedekindInverseIdealOpen.stageMap_range,
      ``ManuscriptAudit.DedekindInverseIdealOpen.isAffineOpen_of_ne_bot] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
