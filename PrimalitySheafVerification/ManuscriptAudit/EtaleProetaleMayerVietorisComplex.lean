import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisHigh
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality
import PrimalitySheafVerification.ManuscriptAudit.SquareShortComplexTransport

/-! The actual Mayer–Vietoris complexes compare under the inverse image of sites. -/

namespace ManuscriptAudit.EtaleProetaleMayerVietorisComplex

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleProetaleSiteInclusion (inclusion)
open EtaleProetaleInverseImage (inverseImage)
open EtaleProetaleFreeRepresentable
open EtaleProetaleFreeRepresentableNaturality
open SquareShortComplexTransport (ofSquare)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev E (X : Scheme.{0}) := Sheaf X.smallEtaleTopology A
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

private theorem etaleMap_eq {X : Scheme.{0}} {U V : X.Etale} (f : U ⟶ V) :
    etaleMap X f = etaleFreeMap X f := by
  apply (etaleSections X U (etaleFree X V)).injective
  have h₁ := etaleSections_precomp X f (𝟙 (etaleFree X V))
  have h₂ := etaleSections_freeMap X f (𝟙 (etaleFree X V))
  rw [Category.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

private theorem proMap_eq {X : Scheme.{0}} {U V : X.ProEt} (f : U ⟶ V) :
    proMap X f = proFreeMap X f := by
  let F := ProetaleMayerVietorisRepresentable.nativeFree V
  apply (proSections X U F).injective
  have h₁ := proSections_precomp X f (𝟙 F)
  have h₂ := proSections_freeMap X f (𝟙 F)
  rw [Category.comp_id] at h₁ h₂
  exact h₁.trans h₂.symm

theorem inverseImageFreeMap_naturality {X : Scheme.{0}} {U V : X.Etale} (f : U ⟶ V) :
    (inverseImage X).map (etaleFreeMap X f) ≫ (inverseImageFreeIso X V).hom =
      (inverseImageFreeIso X U).hom ≫ proFreeMap X ((inclusion X).map f) := by
  rw [← etaleMap_eq, ← proMap_eq]
  exact inverseImageFreeIso_naturality X f

private abbrev etaleFreeFunctor (X : Scheme.{0}) :
    AsSmall.{1} X.Etale ⥤ Sheaf (etaleTopology X) A :=
  yoneda ⋙ (Functor.whiskeringRight (AsSmall.{1} X.Etale)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (etaleTopology X) A

private abbrev proFreeFunctor (X : Scheme.{0}) :
    AsSmall.{1} X.ProEt ⥤ Sheaf (ProetaleMayerVietorisSite.topology X) A :=
  yoneda ⋙ (Functor.whiskeringRight (AsSmall.{1} X.ProEt)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (ProetaleMayerVietorisSite.topology X) A

open EtaleTwoOpenHOne (openArrow identityObject)

variable {U V W X : Scheme.{0}} (j : U ⟶ X) (k : V ⟶ X) (l : W ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (a : Scheme.Etale.mk l ⟶ Scheme.Etale.mk j)
  (b : Scheme.Etale.mk l ⟶ Scheme.Etale.mk k)
  (hD : IsPullback a b (openArrow j) (openArrow k))
  (hCover : Set.range j ∪ Set.range k = Set.univ)

include hD in
private theorem proPullback :
    IsPullback ((inclusion X).map a) ((inclusion X).map b)
      (ProetaleOpenLocalLifts.openArrow j) (ProetaleOpenLocalLifts.openArrow k) :=
  IsPullback.of_isLimit (isLimitPullbackConeMapOfIsLimit (inclusion X) hD.w hD.isLimit)

def proComplex : ShortComplex (P X) :=
  ProetaleMayerVietorisSite.coverComplex j k l ((inclusion X).map a) ((inclusion X).map b)
    (proPullback j k l a b hD) hCover

/-- This isomorphism uses the actual free representable maps and the same oriented overlap. -/
def comparison :
    (EtaleMayerVietorisHigh.coverComplex j k l a b hD hCover).map (inverseImage X) ≅
      proComplex j k l a b hD hCover := by
  let L := inverseImage X
  let E₀ := (etaleSheafEquiv X).inverse
  let P₀ := (ProetaleMayerVietorisSite.sheafEquivalence X).inverse
  letI : L.Additive := L.additive_of_preserves_binary_products
  letI : E₀.Additive := E₀.additive_of_preserves_binary_products
  letI : P₀.Additive := P₀.additive_of_preserves_binary_products
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts E₀
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts P₀
  let S₀ := EtaleMayerVietorisHigh.highSquare j k l a b hD hCover
  let T₀ := ProetaleMayerVietorisSite.openCoverSquare j k l
    ((inclusion X).map a) ((inclusion X).map b) (proPullback j k l a b hD) hCover
  let s₀ := S₀.toSquare.map (etaleFreeFunctor X)
  let t₀ := T₀.toSquare.map (proFreeFunctor X)
  let S := s₀.map E₀
  let T := t₀.map P₀
  let eS : EtaleMayerVietorisHigh.coverComplex j k l a b hD hCover ≅ ofSquare S :=
    SquareShortComplexTransport.mapIso E₀ s₀
  let eT : proComplex j k l a b hD hCover ≅ ofSquare T :=
    SquareShortComplexTransport.mapIso P₀ t₀
  have e : ofSquare (S.map L) ≅ ofSquare T := by
    refine SquareShortComplexTransport.compare _ _
      (inverseImageFreeIso X (Scheme.Etale.mk l)) (inverseImageFreeIso X (Scheme.Etale.mk j))
      (inverseImageFreeIso X (Scheme.Etale.mk k)) (inverseImageFreeIso X (identityObject X))
      ?_ ?_ ?_ ?_
    · exact (inverseImageFreeMap_naturality a).symm
    · exact (inverseImageFreeMap_naturality b).symm
    · exact (inverseImageFreeMap_naturality (openArrow j)).symm
    · exact (inverseImageFreeMap_naturality (openArrow k)).symm
  exact L.mapShortComplex.mapIso eS ≪≫
    SquareShortComplexTransport.mapIso L S ≪≫ e ≪≫ eT.symm

end
end ManuscriptAudit.EtaleProetaleMayerVietorisComplex

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleProetaleMayerVietorisComplex.comparison
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
