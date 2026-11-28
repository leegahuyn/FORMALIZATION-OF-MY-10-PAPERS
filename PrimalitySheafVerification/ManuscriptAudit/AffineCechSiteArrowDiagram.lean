import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCechConerveSiteArrowMaps

/-! The ring arrow diagram gives the actual oppositely oriented
diagram of affine site arrows, with its specified limit cover. -/

namespace ManuscriptAudit.AffineCechSiteArrowDiagram

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineCechConerveSiteComparison (Site siteMap)
open AffineCechConerveSiteArrowMaps (siteSquare)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : CommRingCat.{u}} (P : MorphismProperty Scheme.{u})

private theorem square_id (f : Arrow (Under A))
    (hL : P (Spec.map f.left.hom)) (hR : P (Spec.map f.right.hom)) :
    siteSquare P hL hR hL hR (𝟙 f) = 𝟙 (Arrow.mk (siteMap P f hL hR)) := by
  apply Arrow.hom_ext <;> apply MorphismProperty.Over.Hom.ext <;> exact Spec.map_id _

private theorem square_comp {f g h : Arrow (Under A)}
    (fL : P (Spec.map f.left.hom)) (fR : P (Spec.map f.right.hom))
    (gL : P (Spec.map g.left.hom)) (gR : P (Spec.map g.right.hom))
    (hL : P (Spec.map h.left.hom)) (hR : P (Spec.map h.right.hom))
    (s : f ⟶ g) (t : g ⟶ h) :
    siteSquare P fL fR hL hR (s ≫ t) =
      siteSquare P gL gR hL hR t ≫ siteSquare P fL fR gL gR s := by
  apply Arrow.hom_ext
  · apply MorphismProperty.Over.Hom.ext
    exact Spec.map_comp s.right.right t.right.right
  · apply MorphismProperty.Over.Hom.ext
    exact Spec.map_comp s.left.right t.left.right

/-- Opposite actual site-arrow isomorphism induced by an algebra arrow isomorphism. -/
def siteIsoOfRingIso {f g : Arrow (Under A)}
    (fL : P (Spec.map f.left.hom)) (fR : P (Spec.map f.right.hom))
    (gL : P (Spec.map g.left.hom)) (gR : P (Spec.map g.right.hom))
    (e : f ≅ g) :
    Arrow.mk (siteMap P f fL fR) ≅ Arrow.mk (siteMap P g gL gR) where
  hom := siteSquare P gL gR fL fR e.inv
  inv := siteSquare P fL fR gL gR e.hom
  hom_inv_id := by rw [← square_comp, e.hom_inv_id, square_id]
  inv_hom_id := by rw [← square_comp, e.inv_hom_id, square_id]

variable {J : Type*} [Category* J] (F : J ⥤ Arrow (Under A))
  (hL : ∀ j, P (Spec.map (F.obj j).left.hom))
  (hR : ∀ j, P (Spec.map (F.obj j).right.hom))

/-- The actual affine site arrows reverse each transition of the rings. -/
def diagram : J ⥤ (Arrow (Site (A := A) P))ᵒᵖ where
  obj j := op (Arrow.mk (siteMap P (F.obj j) (hL j) (hR j)))
  map {i j} f := (siteSquare P (hL i) (hR i) (hL j) (hR j) (F.map f)).op
  map_id j := by
    rw [Functor.map_id, square_id, op_id]
  map_comp {i j k} f g := by
    rw [Functor.map_comp, square_comp, op_comp]

variable (c : Cocone F) (cL : P (Spec.map c.pt.left.hom)) (cR : P (Spec.map c.pt.right.hom))

/-- The comparison to the actual limiting cover, not a replacement cover. -/
def cocone : Cocone (diagram P F hL hR) where
  pt := op (Arrow.mk (siteMap P c.pt cL cR))
  ι :=
    { app := fun j ↦ (siteSquare P (hL j) (hR j) cL cR (c.ι.app j)).op
      naturality := by
        intro i j f
        change (siteSquare P (hL i) (hR i) (hL j) (hR j) (F.map f)).op ≫
          (siteSquare P (hL j) (hR j) cL cR (c.ι.app j)).op =
            (siteSquare P (hL i) (hR i) cL cR (c.ι.app i)).op ≫ 𝟙 _
        rw [Category.comp_id, ← op_comp, ← square_comp, c.w] }

end
end ManuscriptAudit.AffineCechSiteArrowDiagram

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineCechSiteArrowDiagram.cocone
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
