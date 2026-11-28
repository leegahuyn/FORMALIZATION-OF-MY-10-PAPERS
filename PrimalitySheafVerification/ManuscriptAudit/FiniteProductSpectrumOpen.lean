import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.Localization.Away.Basic

/-! The genuine component maps of an affine product spectrum are
literal principal open immersions. -/

namespace ManuscriptAudit.FiniteProductSpectrumOpen

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]

/-- The actual map of a factor into the spectrum of the product. -/
abbrev projection (i : ι) : Spec (CommRingCat.of (D i)) ⟶ Spec (CommRingCat.of (∀ j, D j)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom D i))

private theorem isLocalization_single [DecidableEq ι] (i : ι) :
    letI : Algebra (∀ j, D j) (D i) := (Pi.evalRingHom D i).toAlgebra
    IsLocalization.Away (Pi.single i (1 : D i)) (D i) := by
  letI : Algebra (∀ j, D j) (D i) := (Pi.evalRingHom D i).toAlgebra
  apply IsLocalization.Away.mk (Pi.single i (1 : D i))
  · change IsUnit (Pi.single i (1 : D i) i)
    simp
  · intro x
    refine ⟨0, Pi.single i x, ?_⟩
    change x * (Pi.single i (1 : D i) i) ^ 0 = Pi.single i x i
    simp
  · intro x y hxy
    refine ⟨1, ?_⟩
    change x i = y i at hxy
    rw [pow_one]
    funext j
    change Pi.single i (1 : D i) j * x j = Pi.single i (1 : D i) j * y j
    by_cases h : j = i
    · subst j
      rw [hxy]
    · simp [Pi.single_eq_of_ne h]

theorem projection_isOpenImmersion (i : ι) : IsOpenImmersion (projection D i) := by
  classical
  letI : Algebra (∀ j, D j) (D i) := (Pi.evalRingHom D i).toAlgebra
  letI : IsLocalization.Away (Pi.single i (1 : D i)) (D i) := isLocalization_single D i
  exact IsOpenImmersion.of_isLocalization (Pi.single i (1 : D i))

/-- The actual component maps cover the entire finite product spectrum. -/
theorem exists_component [Finite ι] (x : Spec (CommRingCat.of (∀ i, D i))) :
    ∃ (i : ι) (y : Spec (CommRingCat.of (D i))), projection D i y = x := by
  obtain ⟨⟨i, y⟩, hy⟩ := (PrimeSpectrum.sigmaToPiHomeo D).surjective x
  rw [PrimeSpectrum.sigmaToPiHomeo_apply, PrimeSpectrum.sigmaToPi_apply] at hy
  exact ⟨i, y, hy⟩

end
end ManuscriptAudit.FiniteProductSpectrumOpen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteProductSpectrumOpen.projection_isOpenImmersion,
      ``ManuscriptAudit.FiniteProductSpectrumOpen.exists_component] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
