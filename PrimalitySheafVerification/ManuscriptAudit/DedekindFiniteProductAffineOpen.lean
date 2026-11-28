import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import PrimalitySheafVerification.ManuscriptAudit.DedekindInverseIdealOpen
import PrimalitySheafVerification.ManuscriptAudit.FiniteProductSpectrumOpen

/-! Any open of the actual spectrum of a finite product of Dedekind
domains is affine, by disjoint component restrictions. -/

namespace ManuscriptAudit.DedekindFiniteProductAffineOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteProductSpectrumOpen (projection projection_isOpenImmersion exists_component)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ι : Type u} [Finite ι] (D : ι → Type u) [∀ i, CommRing (D i)]
  [∀ i, IsDedekindDomain (D i)]

private abbrev X := Spec (CommRingCat.of (∀ i, D i))
private abbrev pieces (U : (X D).Opens) (i : ι) := projection D i ⁻¹ᵁ U

set_option maxHeartbeats 2400000 in
/-- An open of a finite product of literal affine Dedekind spectra
is a finite disjoint coproduct of affine opens, hence affine. -/
theorem isAffineOpen (U : (X D).Opens) : IsAffineOpen U := by
  classical
  let W (i : ι) := (pieces D U i).toScheme
  let fᵢ (i : ι) : W i ⟶ U.toScheme := projection D i ∣_ U
  let f : (∐ W) ⟶ U.toScheme := Sigma.desc fᵢ
  letI (i : ι) : IsOpenImmersion (projection D i) := projection_isOpenImmersion D i
  letI (i : ι) : IsAffine (W i) := by
    change IsAffineOpen (pieces D U i)
    by_cases h : pieces D U i = ⊥
    · rw [h]
      exact isAffineOpen_bot _
    · exact DedekindInverseIdealOpen.isAffineOpen_of_ne_bot (D i) (FractionRing (D i))
        (pieces D U i) h
  let e := PrimeSpectrum.sigmaToPiHomeo D
  have hE (i : ι) (x : Spec (CommRingCat.of (D i))) : e ⟨i, x⟩ = projection D i x := by
    rw [PrimeSpectrum.sigmaToPiHomeo_apply, PrimeSpectrum.sigmaToPi_apply] <;> rfl
  have hF (i : ι) (x : W i) :
      (f (Sigma.ι W i x)).val = projection D i x.val := by
    have h := congrArg (fun m : W i ⟶ U.toScheme ↦ m x) (Sigma.ι_desc fᵢ i)
    change f (Sigma.ι W i x) = fᵢ i x at h
    rw [h]
    exact morphismRestrict_base_coe (projection D i) U x
  let O := sigmaOpenCover W
  have hInj : Function.Injective f := by
    intro x y hxy
    obtain ⟨i, p, rfl⟩ := O.exists_eq x
    obtain ⟨j, q, rfl⟩ := O.exists_eq y
    have h := congrArg Subtype.val hxy
    change (f (Sigma.ι W i p)).val = (f (Sigma.ι W j q)).val at h
    rw [hF, hF] at h
    have h' : (⟨i, p.val⟩ : Σ k, PrimeSpectrum (D k)) = ⟨j, q.val⟩ :=
      e.injective ((hE i p.val).trans (h.trans (hE j q.val).symm))
    have hi : i = j := congrArg Sigma.fst h'
    subst j
    have hpq : p = q := Subtype.ext ((projection D i).isOpenEmbedding.injective h)
    rw [hpq]
  have hOpen : IsOpenImmersion f := IsOpenImmersion.of_openCover_source f O hInj (fun i ↦ by
    change IsOpenImmersion (Sigma.ι W i ≫ Sigma.desc fᵢ)
    rw [Sigma.ι_desc]
    exact inferInstanceAs (IsOpenImmersion (projection D i ∣_ U)))
  have hSurj : Surjective f := ⟨fun x ↦ by
    obtain ⟨i, p, hp⟩ := exists_component D x.val
    let y : W i := ⟨p, show projection D i p ∈ U from hp.symm ▸ x.property⟩
    exact ⟨Sigma.ι W i y, Subtype.ext ((hF i y).trans hp)⟩⟩
  letI : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨hOpen, hSurj⟩
  exact IsAffine.of_isIso (inv f)

end
end ManuscriptAudit.DedekindFiniteProductAffineOpen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DedekindFiniteProductAffineOpen.isAffineOpen
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
