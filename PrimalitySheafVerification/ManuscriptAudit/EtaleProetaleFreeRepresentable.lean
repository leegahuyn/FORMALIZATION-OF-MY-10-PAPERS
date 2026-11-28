import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Whiskering
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisRepresentable

/-! Pullback of the free representable at an actual étale object. -/

namespace ManuscriptAudit.EtaleProetaleFreeRepresentable

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleProetaleSiteInclusion (inclusion)
open EtaleProetaleInverseImage (inverseImage directImage adjunction)
open ProetaleMayerVietorisRepresentable (nativeFree)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev E (X : Scheme.{0}) := Sheaf X.smallEtaleTopology A
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable (X : Scheme.{0})

abbrev raisedEtale : X.Etale ≌ AsSmall.{1} X.Etale := AsSmall.equiv
abbrev etaleTopology := (raisedEtale X).inverse.inducedTopology X.smallEtaleTopology

def etaleSheafEquiv : E X ≌ Sheaf (etaleTopology X) A :=
  (raisedEtale X).sheafCongr X.smallEtaleTopology (etaleTopology X) A

private abbrev etaleYoneda (W : X.Etale) :=
  yoneda.obj ((raisedEtale X).functor.obj W)

abbrev highEtaleFree (W : X.Etale) :=
  (presheafToSheaf (etaleTopology X) A).obj (etaleYoneda X W ⋙ AddCommGrpCat.free)

abbrev etaleFree (W : X.Etale) : E X :=
  (etaleSheafEquiv X).inverse.obj (highEtaleFree X W)

private abbrev etaleFreeAdj :=
  (Adjunction.whiskerRight (AsSmall.{1} X.Etale)ᵒᵖ AddCommGrpCat.adj).comp
    (sheafificationAdjunction (etaleTopology X) A)

def etaleSections (W : X.Etale) (F : E X) :
    (etaleFree X W ⟶ F) ≃ F.obj.obj (op W) :=
  ((etaleSheafEquiv X).symm.toAdjunction.homEquiv (highEtaleFree X W) F).trans
    (((etaleFreeAdj X).homEquiv (etaleYoneda X W) ((etaleSheafEquiv X).functor.obj F)).trans
      yonedaEquiv)

theorem etaleSections_natural (W : X.Etale) {F G : E X}
    (f : etaleFree X W ⟶ F) (g : F ⟶ G) :
    etaleSections X W G (f ≫ g) = g.hom.app (op W) (etaleSections X W F f) := by
  let e := etaleSheafEquiv X
  let a := e.symm.toAdjunction
  let b := etaleFreeAdj X
  let T := etaleYoneda X W
  change yonedaEquiv ((b.homEquiv T (e.functor.obj G)) ((a.homEquiv (highEtaleFree X W) G) (f ≫ g))) =
    g.hom.app (op W)
      (yonedaEquiv ((b.homEquiv T (e.functor.obj F)) ((a.homEquiv (highEtaleFree X W) F) f)))
  rw [a.homEquiv_naturality_right, b.homEquiv_naturality_right, yonedaEquiv_comp] <;> rfl

private abbrev proEquiv := ProetaleMayerVietorisSite.sheafEquivalence X
private abbrev proTopology := ProetaleMayerVietorisSite.topology X
private abbrev proYoneda (W : X.ProEt) :=
  yoneda.obj ((ProetaleMayerVietorisSite.siteEquivalence X).functor.obj W)

private abbrev highProFree (W : X.ProEt) :=
  (presheafToSheaf (proTopology X) A).obj (proYoneda X W ⋙ AddCommGrpCat.free)

private abbrev proFreeAdj :=
  (Adjunction.whiskerRight (AsSmall.{1} X.ProEt)ᵒᵖ AddCommGrpCat.adj).comp
    (sheafificationAdjunction (proTopology X) A)

def proSections (W : X.ProEt) (F : P X) :
    (nativeFree W ⟶ F) ≃ F.obj.obj (op W) :=
  ((proEquiv X).symm.toAdjunction.homEquiv (highProFree X W) F).trans
    (((proFreeAdj X).homEquiv (proYoneda X W) ((proEquiv X).functor.obj F)).trans yonedaEquiv)

theorem proSections_natural (W : X.ProEt) {F G : P X}
    (f : nativeFree W ⟶ F) (g : F ⟶ G) :
    proSections X W G (f ≫ g) = g.hom.app (op W) (proSections X W F f) := by
  let e := proEquiv X
  let a := e.symm.toAdjunction
  let b := proFreeAdj X
  let T := proYoneda X W
  change yonedaEquiv ((b.homEquiv T (e.functor.obj G)) ((a.homEquiv (highProFree X W) G) (f ≫ g))) =
    g.hom.app (op W)
      (yonedaEquiv ((b.homEquiv T (e.functor.obj F)) ((a.homEquiv (highProFree X W) F) f)))
  rw [a.homEquiv_naturality_right, b.homEquiv_naturality_right, yonedaEquiv_comp] <;> rfl

private abbrev pullFree (W : X.Etale) := (inverseImage X).obj (etaleFree X W)
private abbrev targetFree (W : X.Etale) := nativeFree ((inclusion X).obj W)

def sectionComparison (W : X.Etale) (F : P X) :
    (pullFree X W ⟶ F) ≃ (targetFree X W ⟶ F) :=
  (((adjunction X).homEquiv (etaleFree X W) F).trans
    (etaleSections X W ((directImage X).obj F))).trans
    (proSections X ((inclusion X).obj W) F).symm

theorem sectionComparison_natural (W : X.Etale) {F G : P X}
    (f : pullFree X W ⟶ F) (g : F ⟶ G) :
    sectionComparison X W G (f ≫ g) = sectionComparison X W F f ≫ g := by
  let W' := (inclusion X).obj W
  let a := adjunction X
  let Γ (T : P X) := etaleSections X W ((directImage X).obj T)
  let β (T : P X) := proSections X W' T
  let e (T : P X) := a.homEquiv (etaleFree X W) T
  apply (β G).injective
  change β G ((β G).symm (Γ G (e G (f ≫ g)))) =
    β G ((β F).symm (Γ F (e F f)) ≫ g)
  rw [Equiv.apply_symm_apply, proSections_natural, Equiv.apply_symm_apply,
    a.homEquiv_naturality_right, etaleSections_natural] <;> rfl

def inverseImageFreeIso (W : X.Etale) :
    (inverseImage X).obj (etaleFree X W) ≅ nativeFree ((inclusion X).obj W) := by
  let e := sectionComparison X W
  let h : pullFree X W ⟶ targetFree X W := (e _).symm (𝟙 _)
  let i : targetFree X W ⟶ pullFree X W := e _ (𝟙 _)
  refine ⟨h, i, ?_, ?_⟩
  · apply (e (pullFree X W)).injective
    change e (pullFree X W) (h ≫ i) = i
    rw [sectionComparison_natural]
    change e (targetFree X W) ((e (targetFree X W)).symm (𝟙 _)) ≫ i = i
    simp only [Equiv.apply_symm_apply, Category.id_comp]
  · have q := sectionComparison_natural X W (𝟙 (pullFree X W)) h
    rw [Category.id_comp] at q
    change e (targetFree X W) h = i ≫ h at q
    rw [← q]
    exact (e (targetFree X W)).apply_symm_apply (𝟙 _)

/-- The actual sheafified Yoneda arrow in the raised étale universe. -/
def etaleFreeMap {U V : X.Etale} (f : U ⟶ V) : etaleFree X U ⟶ etaleFree X V :=
  (etaleSheafEquiv X).inverse.map
    ((((Functor.whiskeringRight (AsSmall.{1} X.Etale)ᵒᵖ _ _).obj AddCommGrpCat.free) ⋙
      presheafToSheaf (etaleTopology X) A).map (yoneda.map ((raisedEtale X).functor.map f)))

theorem etaleSections_freeMap {U V : X.Etale} (f : U ⟶ V) {F : E X}
    (g : etaleFree X V ⟶ F) :
    etaleSections X U F (etaleFreeMap X f ≫ g) =
      F.obj.map f.op (etaleSections X V F g) := by
  let e := etaleSheafEquiv X
  let a := e.symm.toAdjunction
  let b := etaleFreeAdj X
  let y := yoneda.map ((raisedEtale X).functor.map f)
  let H := (Functor.whiskeringRight (AsSmall.{1} X.Etale)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (etaleTopology X) A
  change yonedaEquiv ((b.homEquiv (etaleYoneda X U) (e.functor.obj F))
      ((a.homEquiv (highEtaleFree X U) F) (e.inverse.map (H.map y) ≫ g))) =
    F.obj.map f.op (yonedaEquiv ((b.homEquiv (etaleYoneda X V) (e.functor.obj F))
      ((a.homEquiv (highEtaleFree X V) F) g)))
  have h₁ := a.homEquiv_naturality_left (H.map y) g
  change (a.homEquiv (highEtaleFree X U) F) (e.inverse.map (H.map y) ≫ g) =
    H.map y ≫ (a.homEquiv (highEtaleFree X V) F) g at h₁
  let v := (a.homEquiv (highEtaleFree X V) F) g
  have h₂ := b.homEquiv_naturality_left y v
  change (b.homEquiv (etaleYoneda X U) (e.functor.obj F)) (H.map y ≫ v) =
    y ≫ (b.homEquiv (etaleYoneda X V) (e.functor.obj F)) v at h₂
  rw [h₁, h₂]
  exact (yonedaEquiv_naturality
    ((b.homEquiv (etaleYoneda X V) (e.functor.obj F)) v)
    ((raisedEtale X).functor.map f)).symm

/-- The actual sheafified Yoneda arrow in the raised pro-étale universe. -/
def proFreeMap {U V : X.ProEt} (f : U ⟶ V) : nativeFree U ⟶ nativeFree V :=
  (proEquiv X).inverse.map
    ((((Functor.whiskeringRight (AsSmall.{1} X.ProEt)ᵒᵖ _ _).obj AddCommGrpCat.free) ⋙
      presheafToSheaf (proTopology X) A).map
      (yoneda.map ((ProetaleMayerVietorisSite.siteEquivalence X).functor.map f)))

theorem proSections_freeMap {U V : X.ProEt} (f : U ⟶ V) {F : P X}
    (g : nativeFree V ⟶ F) :
    proSections X U F (proFreeMap X f ≫ g) =
      F.obj.map f.op (proSections X V F g) := by
  let e := proEquiv X
  let a := e.symm.toAdjunction
  let b := proFreeAdj X
  let y := yoneda.map ((ProetaleMayerVietorisSite.siteEquivalence X).functor.map f)
  let H := (Functor.whiskeringRight (AsSmall.{1} X.ProEt)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (proTopology X) A
  change yonedaEquiv ((b.homEquiv (proYoneda X U) (e.functor.obj F))
      ((a.homEquiv (highProFree X U) F) (e.inverse.map (H.map y) ≫ g))) =
    F.obj.map f.op (yonedaEquiv ((b.homEquiv (proYoneda X V) (e.functor.obj F))
      ((a.homEquiv (highProFree X V) F) g)))
  have h₁ := a.homEquiv_naturality_left (H.map y) g
  change (a.homEquiv (highProFree X U) F) (e.inverse.map (H.map y) ≫ g) =
    H.map y ≫ (a.homEquiv (highProFree X V) F) g at h₁
  let v := (a.homEquiv (highProFree X V) F) g
  have h₂ := b.homEquiv_naturality_left y v
  change (b.homEquiv (proYoneda X U) (e.functor.obj F)) (H.map y ≫ v) =
    y ≫ (b.homEquiv (proYoneda X V) (e.functor.obj F)) v at h₂
  rw [h₁, h₂]
  exact (yonedaEquiv_naturality
    ((b.homEquiv (proYoneda X V) (e.functor.obj F)) v)
    ((ProetaleMayerVietorisSite.siteEquivalence X).functor.map f)).symm

end
end ManuscriptAudit.EtaleProetaleFreeRepresentable

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleFreeRepresentable.etaleSections_natural,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentable.proSections_natural,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentable.sectionComparison_natural,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentable.inverseImageFreeIso,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentable.etaleSections_freeMap,
      ``ManuscriptAudit.EtaleProetaleFreeRepresentable.proSections_freeMap] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
