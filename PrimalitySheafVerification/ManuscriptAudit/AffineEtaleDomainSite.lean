import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDomainCover

/-!
# Integral affine charts form a dense étale subsite

An arbitrary affine étale chart over an integrally closed affine domain
is covered by its finite domain factors. The actual arrows are the
spectrum maps of the quotient maps, whose images are the basic opens
at the lifted idempotents.
-/

namespace ManuscriptAudit.AffineEtaleDomainSite

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

variable (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

private abbrev X := Spec (CommRingCat.of A)

/-- The full subcategory of integral affine objects in the actual affine étale site. -/
def integralCharts : ObjectProperty (X A).AffineEtale :=
  fun U ↦ IsDomain (unop U.left)

/-- The fully faithful inclusion of the native integral affine charts. -/
abbrev inclusion := (integralCharts A).ι

private abbrev specAlgebraMap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The integral objects cover the native affine étale site. -/
theorem integralCharts_coverDense :
    (inclusion A).IsCoverDense (Scheme.AffineEtale.topology (X A)) where
  is_cover U := by
    let B : CommRingCat.{u} := unop U.left
    obtain ⟨a, ha⟩ := Spec.map_surjective U.hom
    letI : Algebra A B := a.hom.toAlgebra
    have he : Etale (Spec.map a) := ha.symm ▸ U.prop
    letI : Algebra.Etale A B := RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp he)
    have ha' : specAlgebraMap A B = U.hom :=
      (congrArg Spec.map (CommRingCat.ofHom_hom a)).trans ha
    obtain ⟨I, hI, e, hDom, hEt, hLoc, hCover⟩ :=
      AffineEtaleDomainFactors.exists_etale_domain_cover A B (FractionRing A)
    letI : Finite I := hI
    let D (i : I) := B ⧸ Ideal.span {1 - e i}
    let V (i : I) : (integralCharts A).FullSubcategory := by
      letI : Algebra.Etale A (D i) := hEt i
      letI : Etale (specAlgebraMap A (D i)) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (RingHom.etale_algebraMap.mpr inferInstance)
      exact ⟨Scheme.AffineEtale.mk (specAlgebraMap A (D i)), hDom i⟩
    let C (i : I) := (inclusion A).obj (V i)
    let f (i : I) : C i ⟶ U := by
      refine MorphismProperty.CostructuredArrow.homMk
        (CommRingCat.ofHom (algebraMap B (D i))).op trivial ?_
      change specAlgebraMap B (D i) ≫ U.hom = specAlgebraMap A (D i)
      rw [← ha', ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact (IsScalarTower.algebraMap_eq A B (D i)).symm
    let G := Scheme.AffineEtale.Spec (X A)
    have hf : Sieve.ofArrows C f ∈ Scheme.AffineEtale.topology (X A) U := by
      apply (G.functorPushforward_mem_iff (Scheme.AffineEtale.topology (X A))
        (X A).smallEtaleTopology).mp
      rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
      apply Set.eq_univ_iff_forall.mpr
      intro x
      obtain ⟨i, hx⟩ := hCover x
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      letI : IsLocalization.Away (e i) (D i) := hLoc i
      change x ∈ Set.range (specAlgebraMap B (D i))
      have hm (z : Spec (CommRingCat.of (D i))) :
          specAlgebraMap B (D i) z = PrimeSpectrum.comap (algebraMap B (D i)) z :=
        Spec.map_apply (CommRingCat.ofHom (algebraMap B (D i))) z
      have hr : Set.range (specAlgebraMap B (D i)) =
          Set.range (PrimeSpectrum.comap (algebraMap B (D i))) :=
        congrArg Set.range (funext hm)
      rw [hr, PrimeSpectrum.localization_away_comap_range (D i) (e i)]
      exact hx
    apply (Scheme.AffineEtale.topology (X A)).superset_covering _ hf
    apply Sieve.generate_le_iff.mpr
    apply Presieve.ofArrows_le_iff.mpr
    intro i
    exact Presieve.in_coverByImage (inclusion A) (Y := V i) (f i)

end

end ManuscriptAudit.AffineEtaleDomainSite

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineEtaleDomainSite.integralCharts_coverDense
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
