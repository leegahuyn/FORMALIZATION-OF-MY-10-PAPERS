import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Sites.Equivalence
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionComposition

/-!
# Étale cohomology under an actual scheme isomorphism

Postcomposition by the isomorphism and its inverse identifies the
small étale categories and their covering families. The induced
equivalence of abelian sheaves is restriction along the inverse
isomorphism, so it carries constants to constants and identifies
their ordinary cohomology in every degree.
-/

namespace ManuscriptAudit.SmallEtaleEquivalenceCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open OpenEtaleExtension GeometricSkyscraperCohomology

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private abbrev C := AddCommGrpCat.{u}

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The actual étale site equivalence induced by an isomorphism of schemes. -/
def schemeIsoEtaleEquivalence : X.Etale ≌ Y.Etale := by
  let F := etalePostcompose e.hom
  let G := etalePostcompose e.inv
  let hf : Etale e.hom := inferInstance
  let hg : Etale e.inv := inferInstance
  let unit : 𝟭 X.Etale ≅ F ⋙ G :=
    (MorphismProperty.Over.mapId (P := @Etale) ⊤ X (e.hom ≫ e.inv) e.hom_inv_id).symm ≪≫
      MorphismProperty.Over.mapComp (P := @Etale) ⊤ hf hg
  let counit : G ⋙ F ≅ 𝟭 Y.Etale :=
    (MorphismProperty.Over.mapComp (P := @Etale) ⊤ hg hf).symm ≪≫
      MorphismProperty.Over.mapId (P := @Etale) ⊤ Y (e.inv ≫ e.hom) e.inv_hom_id
  exact CategoryTheory.Equivalence.mk F G unit counit

/-- The inverse on étale objects reflects and preserves the native covering sieves. -/
theorem schemeIsoInverse_isDenseSubsite :
    (schemeIsoEtaleEquivalence e).inverse.IsDenseSubsite Y.smallEtaleTopology X.smallEtaleTopology where
  functorPushforward_mem_iff {W R} := by
    obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff,
      Scheme.ofArrows_mem_smallEtaleTopology_iff]
    change (⋃ i, Set.range (f i).left) = Set.univ ↔
      (⋃ i, Set.range (f i).left) = Set.univ
    rfl

/-- The equivalence on abelian sheaves induced by the actual scheme isomorphism. -/
def schemeIsoSheafEquivalence : Sheaf X.smallEtaleTopology C.{u} ≌ Sheaf Y.smallEtaleTopology C.{u} :=
  let E := schemeIsoEtaleEquivalence e
  letI : E.inverse.IsDenseSubsite Y.smallEtaleTopology X.smallEtaleTopology :=
    schemeIsoInverse_isDenseSubsite e
  E.sheafCongr X.smallEtaleTopology Y.smallEtaleTopology C.{u}

private def schemeIsoConstantComparison :
    constantSheaf X.smallEtaleTopology C.{u} ⋙ (schemeIsoSheafEquivalence e).functor ≅
      constantSheaf Y.smallEtaleTopology C.{u} :=
  restrictionConstantIso e.inv

/-- The ordinary constant-coefficient étale cohomology groups of
isomorphic schemes agree in every degree and in every universe. -/
def schemeIsoCohomologyEquiv (M : C.{u}) (n : ℕ) :
    Sheaf.H ((constantSheaf X.smallEtaleTopology C.{u}).obj M) n ≃+
      Sheaf.H ((constantSheaf Y.smallEtaleTopology C.{u}).obj M) n := by
  let A := Sheaf X.smallEtaleTopology C.{u}
  let B := Sheaf Y.smallEtaleTopology C.{u}
  letI : IsGrothendieckAbelian.{u} A :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X C.{u}
  letI : EnoughInjectives A := IsGrothendieckAbelian.enoughInjectives.{u} (C := A)
  let F : A ⥤ B := (schemeIsoSheafEquivalence e).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let T := AddCommGrpCat.of (ULift.{u} ℤ)
  let Z := (constantSheaf X.smallEtaleTopology C.{u}).obj T
  let G := (constantSheaf X.smallEtaleTopology C.{u}).obj M
  let c := schemeIsoConstantComparison e
  let e₀ := AddEquiv.ofBijective (F.mapExtAddHom Z G n)
    (F.mapExt_bijective_of_preservesInjectiveObjects Z G n)
  let d := ((extFunctor (C := B) n).mapIso (c.app T).symm.op).app (F.obj G)
  let e₁ := d.addCommGroupIsoToAddEquiv
  let e₂ := ((Sheaf.functorH Y.smallEtaleTopology n).mapIso (c.app M)).addCommGroupIsoToAddEquiv
  exact e₀.trans (e₁.trans e₂)

end

end ManuscriptAudit.SmallEtaleEquivalenceCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleEquivalenceCohomology.schemeIsoEtaleEquivalence,
      ``ManuscriptAudit.SmallEtaleEquivalenceCohomology.schemeIsoInverse_isDenseSubsite,
      ``ManuscriptAudit.SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
