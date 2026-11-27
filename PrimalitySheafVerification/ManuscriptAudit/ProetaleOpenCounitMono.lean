import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension
import PrimalitySheafVerification.ManuscriptAudit.DownwardClosedLanCounit

/-! On the native pro-étale site, the sheafified extension-by-zero
counit is monic for every open immersion and every abelian sheaf. -/

namespace ManuscriptAudit.ProetaleOpenCounitMono

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{1}
private abbrev P := proetalePostcompose j
private abbrev L := (P j).op
private abbrev J := Scheme.ProEt.topology X

local instance postFull : (P j).Full := (postcomposeFullyFaithful j).full
local instance postFaithful : (P j).Faithful := (postcomposeFullyFaithful j).faithful
local instance hasLan (F : U.ProEtᵒᵖ ⥤ A) : (L j).HasLeftKanExtension F :=
  hasLeftKanExtension j A F
local instance hasPointwise (F : U.ProEtᵒᵖ ⥤ A) : (L j).HasPointwiseLeftKanExtension F :=
  hasPointwiseLeftKanExtension j A F

private theorem downward_closed (W : X.ProEtᵒᵖ) (a : CostructuredArrow (L j) W) :
    ∃ V : U.ProEtᵒᵖ, Nonempty ((L j).obj V ≅ W) := by
  let Y := a.left.unop
  let g : W.unop ⟶ (P j).obj Y := a.hom.unop
  have h : (g.left ≫ Y.hom) ≫ j = W.unop.hom := by
    simpa only [Category.assoc, MorphismProperty.Over.map_obj_hom] using
      MorphismProperty.Over.w g
  letI : WeaklyEtale ((g.left ≫ Y.hom) ≫ j) := by
    rw [h]
    exact W.unop.prop
  let V : U.ProEt := MorphismProperty.Over.mk ⊤ (g.left ≫ Y.hom) (WeaklyEtale.of_comp _ j)
  let e : (P j).obj V ≅ W.unop := MorphismProperty.Over.isoMk (Iso.refl W.unop.left) (by
    change 𝟙 W.unop.left ≫ W.unop.hom = (g.left ≫ Y.hom) ≫ j
    simpa only [Category.id_comp] using h.symm)
  exact ⟨op V, ⟨e.op.symm⟩⟩

abbrev rawCounit (F : Sheaf (J (X := X)) A) :=
  DownwardClosedLanCounit.counit (L j) F.obj

private theorem raw_mono (F : Sheaf (J (X := X)) A) : Mono (rawCounit j F) := by
  apply (NatTrans.mono_iff_mono_app (rawCounit j F)).2
  intro W
  exact DownwardClosedLanCounit.counit_component_mono (L j) F.obj (downward_closed j) W

/-- On a chart factoring through the open, the raw counit is an isomorphism. -/
theorem rawCounit_isIso_on_range (F : Sheaf (J (X := X)) A) (W : X.ProEt)
    (h : Set.range W.hom ⊆ Set.range j) : IsIso ((rawCounit j F).app (op W)) := by
  let g := IsOpenImmersion.lift j W.hom h
  have hg : g ≫ j = W.hom := IsOpenImmersion.lift_fac _ _ _
  letI : WeaklyEtale (g ≫ j) := hg.symm ▸ W.prop
  let V := MorphismProperty.Over.mk ⊤ g (WeaklyEtale.of_comp g j)
  let e : (P j).obj V ≅ W := MorphismProperty.Over.isoMk (Iso.refl W.left) (by
    change 𝟙 W.left ≫ W.hom = g ≫ j
    rw [Category.id_comp, hg])
  exact DownwardClosedLanCounit.counit_at_iso_isIso (L j) F.obj e.op.symm

/-- The map from the actual native extension of an open restriction to the given sheaf. -/
def extensionRestrictionMap (F : Sheaf (J (X := X)) A) :
    (extensionByZero j A).obj ((restriction j A).obj F) ⟶ F :=
  (presheafToSheaf (J (X := X)) A).map (rawCounit j F) ≫ (sheafificationIso F).inv

theorem extensionRestrictionMap_mono (F : Sheaf (J (X := X)) A) :
    Mono (extensionRestrictionMap j F) := by
  letI : Mono (rawCounit j F) := raw_mono j F
  change Mono ((presheafToSheaf (J (X := X)) A).map (rawCounit j F) ≫ (sheafificationIso F).inv)
  infer_instance

/-- Local surjectivity of the raw counit identifies the actual sheafified extension. -/
theorem extensionRestrictionMap_isIso (F : Sheaf (J (X := X)) A)
    (h : Presheaf.IsLocallySurjective (J (X := X)) (rawCounit j F)) :
    IsIso (extensionRestrictionMap j F) := by
  letI := h
  letI : Presheaf.IsLocallyInjective (J (X := X)) (rawCounit j F) := ⟨by
    intro W a b hab
    have hm := (NatTrans.mono_iff_mono_app (rawCounit j F)).mp (raw_mono j F) W
    have hEq := (AddCommGrpCat.mono_iff_injective _).mp hm hab
    subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact (J (X := X)).top_mem _⟩
  let Q := presheafToSheaf (J (X := X)) A
  letI : IsIso (Q.map (rawCounit j F)) :=
    ((J (X := X)).W_iff (rawCounit j F)).mp
      ((J (X := X)).W_of_isLocallyBijective (rawCounit j F))
  change IsIso (Q.map (rawCounit j F) ≫ (sheafificationIso F).inv)
  infer_instance

end

end ManuscriptAudit.ProetaleOpenCounitMono

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenCounitMono.extensionRestrictionMap_mono,
      ``ManuscriptAudit.ProetaleOpenCounitMono.rawCounit_isIso_on_range,
      ``ManuscriptAudit.ProetaleOpenCounitMono.extensionRestrictionMap_isIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
