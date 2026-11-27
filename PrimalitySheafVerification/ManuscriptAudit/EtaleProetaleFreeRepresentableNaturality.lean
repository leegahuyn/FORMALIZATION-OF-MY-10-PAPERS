import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleFreeRepresentable

/-! Naturality in the representing object of the actual pullback isomorphism. -/

namespace ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleProetaleSiteInclusion (inclusion)
open EtaleProetaleInverseImage (inverseImage directImage adjunction)
open EtaleProetaleFreeRepresentable
open ProetaleMayerVietorisRepresentable (nativeFree)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev E (X : Scheme.{0}) := Sheaf X.smallEtaleTopology A
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable (X : Scheme.{0})

def etaleMap {U V : X.Etale} (f : U ⟶ V) : etaleFree X U ⟶ etaleFree X V :=
  (etaleSections X U (etaleFree X V)).symm
    ((etaleFree X V).obj.map f.op (etaleSections X V (etaleFree X V) (𝟙 _)))

def proMap {U V : X.ProEt} (f : U ⟶ V) : nativeFree U ⟶ nativeFree V :=
  (proSections X U (nativeFree V)).symm
    ((nativeFree V).obj.map f.op (proSections X V (nativeFree V) (𝟙 _)))

theorem etaleSections_precomp {U V : X.Etale} (f : U ⟶ V) {F : E X}
    (g : etaleFree X V ⟶ F) :
    etaleSections X U F (etaleMap X f ≫ g) = F.obj.map f.op (etaleSections X V F g) := by
  rw [etaleSections_natural]
  unfold etaleMap
  rw [Equiv.apply_symm_apply, NatTrans.naturality_apply]
  rw [← etaleSections_natural, Category.id_comp]

theorem proSections_precomp {U V : X.ProEt} (f : U ⟶ V) {F : P X}
    (g : nativeFree V ⟶ F) :
    proSections X U F (proMap X f ≫ g) = F.obj.map f.op (proSections X V F g) := by
  rw [proSections_natural]
  unfold proMap
  rw [Equiv.apply_symm_apply, NatTrans.naturality_apply]
  rw [← proSections_natural, Category.id_comp]

theorem sectionComparison_precomp {U V : X.Etale} (f : U ⟶ V) {F : P X}
    (h : (inverseImage X).obj (etaleFree X V) ⟶ F) :
    sectionComparison X U F ((inverseImage X).map (etaleMap X f) ≫ h) =
      proMap X ((inclusion X).map f) ≫ sectionComparison X V F h := by
  let W := (inclusion X).obj U
  let W' := (inclusion X).obj V
  let a := adjunction X
  let F₀ := (directImage X).obj F
  apply (proSections X W F).injective
  change proSections X W F
      ((proSections X W F).symm (etaleSections X U F₀
        ((a.homEquiv (etaleFree X U) F) ((inverseImage X).map (etaleMap X f) ≫ h)))) =
    proSections X W F (proMap X ((inclusion X).map f) ≫
      (proSections X W' F).symm (etaleSections X V F₀ ((a.homEquiv (etaleFree X V) F) h)))
  rw [Equiv.apply_symm_apply, proSections_precomp, Equiv.apply_symm_apply,
    a.homEquiv_naturality_left, etaleSections_precomp] <;> rfl

private theorem compare_iso_hom (U : X.Etale) :
    sectionComparison X U (nativeFree ((inclusion X).obj U)) (inverseImageFreeIso X U).hom =
      𝟙 (nativeFree ((inclusion X).obj U)) := by
  change (sectionComparison X U _)
    ((sectionComparison X U _).symm (𝟙 _)) = _
  exact Equiv.apply_symm_apply _ _

theorem inverseImageFreeIso_naturality {U V : X.Etale} (f : U ⟶ V) :
    (inverseImage X).map (etaleMap X f) ≫ (inverseImageFreeIso X V).hom =
      (inverseImageFreeIso X U).hom ≫ proMap X ((inclusion X).map f) := by
  apply (sectionComparison X U (nativeFree ((inclusion X).obj V))).injective
  rw [sectionComparison_precomp, sectionComparison_natural, compare_iso_hom X V,
    compare_iso_hom X U, Category.comp_id, Category.id_comp]

end
end ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality.etaleSections_precomp,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality.proSections_precomp,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality.sectionComparison_precomp,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality.inverseImageFreeIso_naturality] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
