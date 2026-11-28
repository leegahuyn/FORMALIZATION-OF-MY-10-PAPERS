import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Whiskering
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionComposition

/-! True open-site restriction commutes with abelian sheafification.
The comparison is characterized by the actual unit of sheafification. -/

namespace ManuscriptAudit.OpenEtaleSheafification

open AlgebraicGeometry CategoryTheory Opposite
open OpenEtaleExtension SmallEtaleBaseChange

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{u}
private abbrev L (Y : Scheme.{u}) := presheafToSheaf Y.smallEtaleTopology A.{u}
private abbrev P (Y : Scheme.{u}) := sheafToPresheaf Y.smallEtaleTopology A.{u}
private abbrev s (Y : Scheme.{u}) := sheafificationAdjunction Y.smallEtaleTopology A.{u}

/-- Literal restriction of an actual presheaf to the open site. -/
abbrev precompose :=
  (Functor.whiskeringLeft U.Etaleᵒᵖ X.Etaleᵒᵖ A.{u}).obj (etalePostcompose j).op

private abbrev push :=
  (Functor.whiskeringLeft X.Etaleᵒᵖ U.Etaleᵒᵖ A.{u}).obj (etaleBaseChange j).op

private abbrev R := restriction j A.{u}
private abbrev D := directImage j A.{u}

private def siteAdj : etalePostcompose j ⊣ etaleBaseChange j :=
  MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ j
    (show Etale j from inferInstance) trivial

private def presheafAdj : precompose j ⊣ push j :=
  (siteAdj j).op.whiskerLeft A.{u}

private def openAdj : precompose j ⋙ L U ⊣ D j ⋙ P X :=
  (presheafAdj j).comp (s U)

private def ambientAdj : L X ⋙ R j ⊣ D j ⋙ P X :=
  (s X).comp (restrictionDirectImageAdjunction j)

/-- Restricting before or after sheafification gives canonically
isomorphic actual sheaves on the open. -/
def comparison : precompose j ⋙ L U ≅ L X ⋙ R j :=
  (openAdj j).leftAdjointUniq (ambientAdj j)

/-- The actual comparison is the unique factorization of the restricted
ambient sheafification unit through sheafification on the open. -/
theorem comparison_unit (F : X.Etaleᵒᵖ ⥤ A.{u}) :
    (s U).homEquiv ((precompose j).obj F) ((R j).obj ((L X).obj F))
        ((comparison j).hom.app F) =
      (precompose j).map ((s X).unit.app F) := by
  let a := presheafAdj j
  let x := (s X).unit.app F
  let T := ((R j).obj ((L X).obj F)).obj
  apply (a.homEquiv F T).injective
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (openAdj j) (ambientAdj j) F
  change ((a.comp (s U)).homEquiv F ((R j).obj ((L X).obj F)))
        ((comparison j).hom.app F) = (ambientAdj j).unit.app F at h
  rw [Adjunction.comp_homEquiv] at h
  have hUnit : (ambientAdj j).unit.app F =
      x ≫ a.unit.app ((L X).obj F).obj := by
    unfold ambientAdj
    rw [Adjunction.comp_unit_app]
    rfl
  rw [hUnit] at h
  have hn : (a.homEquiv F T) ((precompose j).map x) =
      x ≫ a.unit.app ((L X).obj F).obj := by
    rw [Adjunction.homEquiv_unit]
    exact (a.unit.naturality x).symm
  exact h.trans hn.symm

/-- Applying a genuine map from a presheaf to a sheaf is compatible with
the explicit restriction and sheafification comparison. -/
theorem comparison_postcompose (F : X.Etaleᵒᵖ ⥤ A.{u})
    (G : Sheaf X.smallEtaleTopology A.{u}) (g : F ⟶ G.obj) :
    (s U).homEquiv ((precompose j).obj F) ((R j).obj G)
      ((comparison j).hom.app F ≫ (R j).map (((s X).homEquiv F G).symm g)) =
    (precompose j).map g := by
  let f := ((s X).homEquiv F G).symm g
  have hf : (s X).unit.app F ≫ f.hom = g := by
    rw [← (s X).homEquiv_unit]
    exact ((s X).homEquiv F G).apply_symm_apply g
  rw [(s U).homEquiv_naturality_right, comparison_unit]
  change (precompose j).map ((s X).unit.app F) ≫ (precompose j).map f.hom = _
  rw [← Functor.map_comp, hf]

end

end ManuscriptAudit.OpenEtaleSheafification

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleSheafification.comparison_unit,
      ``ManuscriptAudit.OpenEtaleSheafification.comparison_postcompose] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
