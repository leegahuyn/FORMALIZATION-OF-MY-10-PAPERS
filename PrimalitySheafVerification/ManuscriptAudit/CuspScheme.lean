import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Topology.Homeomorph.Lemmas
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta

/-!
# The affine cusp inclusion as a morphism of schemes

The finite map on spectra induced by (K[X^2,X^3]subset K[X]) is
surjective and universally injective. The field-point test uses the
actual coordinate inclusion rather than a model of the cusp's stalks.
-/

namespace ManuscriptAudit.CuspScheme

open AlgebraicGeometry CategoryTheory CategoryTheory.MorphismProperty Polynomial

universe u v

variable (K : Type u) [Field K]

private noncomputable abbrev cuspAlgebra : Subalgebra K (Polynomial K) :=
  Algebra.adjoin K ({(X : Polynomial K) ^ 2, X ^ 3} : Set (Polynomial K))

private noncomputable abbrev cuspRing := cuspAlgebra K

/-- The coordinate inclusion as an arrow in commutative rings. -/
noncomputable def inclusion : CommRingCat.of (cuspRing K) ⟶ CommRingCat.of (Polynomial K) :=
  CommRingCat.ofHom (algebraMap (cuspRing K) (Polynomial K))

/-- The actual induced morphism of affine schemes. -/
noncomputable def cuspMap :
    Spec (CommRingCat.of (Polynomial K)) ⟶ Spec (CommRingCat.of (cuspRing K)) :=
  Spec.map (inclusion K)

variable (L : Type v) [Field L]

private noncomputable def restrictRing (f : Polynomial K →+* L) : cuspRing K →+* L :=
  f.comp (algebraMap (cuspRing K) (Polynomial K))

/-- Field-valued ring maps have unique lifts, including when the
coefficient-field algebra structure is induced by the given map. -/
theorem paper2_cusp_field_ring_points_bijective :
    Function.Bijective (restrictRing K L) := by
  constructor
  · intro f g h
    letI : Algebra K L := (f.comp (algebraMap K (Polynomial K))).toAlgebra
    let fA : Polynomial K →ₐ[K] L := ⟨f, fun _ => rfl⟩
    let gA : Polynomial K →ₐ[K] L := ⟨g, fun r =>
      (DFunLike.congr_fun h (algebraMap K (cuspRing K) r)).symm⟩
    have hA : CuspDelta.cuspRestriction K L fA = CuspDelta.cuspRestriction K L gA := by
      exact AlgHom.ext (fun a => DFunLike.congr_fun h a)
    exact congrArg AlgHom.toRingHom ((CuspDelta.paper2_cusp_field_points_bijective K L).1 hA)
  · intro h
    letI : Algebra K L := (h.comp (algebraMap K (cuspRing K))).toAlgebra
    let hA : cuspRing K →ₐ[K] L := ⟨h, fun _ => rfl⟩
    obtain ⟨g, hg⟩ := (CuspDelta.paper2_cusp_field_points_bijective K L).2 hA
    exact ⟨g.toRingHom, congrArg AlgHom.toRingHom hg⟩

theorem paper2_cusp_map_finite : IsFinite (cuspMap K) := by
  apply (IsFinite.SpecMap_iff (inclusion K)).2
  exact RingHom.finite_algebraMap.mpr (CuspDelta.paper2_cusp_inclusion_finite K)

theorem paper2_cusp_map_universally_injective : UniversallyInjective (cuspMap K) := by
  apply ((tfae_universallyInjective (cuspMap K)).out 1 0).mp
  intro F _ f g h
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  have he : Spec.map (inclusion K ≫ f') = Spec.map (inclusion K ≫ g') := by
    simpa only [Spec.map_comp, cuspMap] using h
  have hRing := congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  have hFG := (paper2_cusp_field_ring_points_bijective K F).1 hRing
  have hf' : f' = g' := CommRingCat.hom_ext hFG
  rw [hf']

theorem paper2_cusp_map_surjective : Surjective (cuspMap K) := by
  rw [surjective_iff]
  intro y
  let Y := Spec (CommRingCat.of (cuspRing K))
  let κ := Y.residueField y
  obtain ⟨f, hf⟩ := Spec.map_surjective (Y.fromSpecResidueField y)
  obtain ⟨g, hg⟩ := (paper2_cusp_field_ring_points_bijective K κ).2 f.hom
  let ψ := Spec.map (CommRingCat.ofHom g)
  have hcomp : ψ ≫ cuspMap K = Y.fromSpecResidueField y := by
    rw [← hf]
    change Spec.map (CommRingCat.ofHom g) ≫ Spec.map (inclusion K) = Spec.map f
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hg)
  obtain ⟨z⟩ : Nonempty (Spec κ) := inferInstance
  refine ⟨ψ z, ?_⟩
  rw [← Scheme.Hom.comp_apply, hcomp, Scheme.fromSpecResidueField_apply]

/-- Every base change of the affine cusp inclusion is a homeomorphism. -/
theorem paper2_cusp_universal_homeomorphism :
    (topologically @IsHomeomorph).universally (cuspMap K) := by
  intro X' Y' i₁ i₂ f' h
  letI : IsFinite (cuspMap K) := paper2_cusp_map_finite K
  letI : Surjective f' := of_isPullback h.flip (paper2_cusp_map_surjective K)
  letI : UniversallyInjective f' :=
    of_isPullback h.flip (paper2_cusp_map_universally_injective K)
  letI : UniversallyClosed f' :=
    of_isPullback h.flip (inferInstance : UniversallyClosed (cuspMap K))
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f'.continuous, f'.isClosedMap, ⟨f'.injective, f'.surjective⟩⟩

end ManuscriptAudit.CuspScheme

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspScheme.paper2_cusp_field_ring_points_bijective,
      ``ManuscriptAudit.CuspScheme.paper2_cusp_map_finite,
      ``ManuscriptAudit.CuspScheme.paper2_cusp_map_universally_injective,
      ``ManuscriptAudit.CuspScheme.paper2_cusp_map_surjective,
      ``ManuscriptAudit.CuspScheme.paper2_cusp_universal_homeomorphism] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
