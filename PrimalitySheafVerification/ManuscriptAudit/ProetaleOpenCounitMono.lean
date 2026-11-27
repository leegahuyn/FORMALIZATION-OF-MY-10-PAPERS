import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
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

private abbrev raw (F : Sheaf (J (X := X)) A) :=
  DownwardClosedLanCounit.counit (L j) F.obj

private theorem raw_mono (F : Sheaf (J (X := X)) A) : Mono (raw j F) := by
  apply (NatTrans.mono_iff_mono_app (raw j F)).2
  intro W
  exact DownwardClosedLanCounit.counit_component_mono (L j) F.obj (downward_closed j) W

/-- The map from the actual native extension of an open restriction to the given sheaf. -/
def extensionRestrictionMap (F : Sheaf (J (X := X)) A) :
    (extensionByZero j A).obj ((restriction j A).obj F) ⟶ F :=
  (presheafToSheaf (J (X := X)) A).map (raw j F) ≫ (sheafificationIso F).inv

theorem extensionRestrictionMap_mono (F : Sheaf (J (X := X)) A) :
    Mono (extensionRestrictionMap j F) := by
  letI : Mono (raw j F) := raw_mono j F
  change Mono ((presheafToSheaf (J (X := X)) A).map (raw j F) ≫ (sheafificationIso F).inv)
  infer_instance

end

end ManuscriptAudit.ProetaleOpenCounitMono

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleOpenCounitMono.extensionRestrictionMap_mono
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
