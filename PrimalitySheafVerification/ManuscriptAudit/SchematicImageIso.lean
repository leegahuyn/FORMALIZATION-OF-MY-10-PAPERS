import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! A commuting square of actual source and target scheme isomorphisms
induces an isomorphism of the native schematic images. -/

namespace ManuscriptAudit.SchematicImageIso

open AlgebraicGeometry CategoryTheory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : X' ⟶ Y') (a : X' ≅ X) (b : Y' ≅ Y)
variable (h : a.hom ≫ f = g ≫ b.hom)

private theorem ker_imageι {U V : Scheme.{u}} (q : U ⟶ V) :
    q.imageι.ker = q.ker :=
  q.ker.ker_subschemeι

include h in
private theorem lift_kernel :
    f.imageι.ker ≤ (g.imageι ≫ b.hom).ker := by
  have ht : f.ker = (g ≫ b.hom).ker :=
    (Scheme.Hom.ker_comp_of_isIso a.hom f).symm.trans (congrArg Scheme.Hom.ker h)
  rw [ker_imageι, Scheme.Hom.ker_comp, ker_imageι, ← Scheme.Hom.ker_comp]
  exact ht.le

private def liftToImage : g.image ⟶ f.image :=
  IsClosedImmersion.lift f.imageι (g.imageι ≫ b.hom) (lift_kernel f g a b h)

set_option maxHeartbeats 900000 in
private theorem liftToImage_fac :
    liftToImage f g a b h ≫ f.imageι = g.imageι ≫ b.hom :=
  IsClosedImmersion.lift_fac _ _ _

include h in
private theorem inverse_square :
    a.inv ≫ g = f ≫ b.inv := by
  apply (cancel_mono b.hom).mp
  calc
    (a.inv ≫ g) ≫ b.hom = a.inv ≫ (g ≫ b.hom) := Category.assoc _ _ _
    _ = a.inv ≫ a.hom ≫ f := congrArg (a.inv ≫ ·) h.symm
    _ = f := Iso.inv_hom_id_assoc a f
    _ = (f ≫ b.inv) ≫ b.hom := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The commuting actual scheme isomorphisms restrict to their native schematic images. -/
def imageIso : g.image ≅ f.image where
  hom := liftToImage f g a b h
  inv := liftToImage g f a.symm b.symm (inverse_square f g a b h)
  hom_inv_id := by
    apply (cancel_mono g.imageι).mp
    rw [Category.assoc, liftToImage_fac, Category.id_comp, ← Category.assoc,
      liftToImage_fac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    apply (cancel_mono f.imageι).mp
    rw [Category.assoc, liftToImage_fac, Category.id_comp, ← Category.assoc,
      liftToImage_fac, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem imageIso_imageι :
    (imageIso f g a b h).hom ≫ f.imageι = g.imageι ≫ b.hom :=
  liftToImage_fac f g a b h

/-- The scheme-image isomorphism intertwines the actual dense affine inclusions. -/
theorem toImage_imageIso :
    g.toImage ≫ (imageIso f g a b h).hom = a.hom ≫ f.toImage := by
  apply (cancel_mono f.imageι).mp
  rw [Category.assoc, imageIso_imageι, ← Category.assoc, Scheme.Hom.toImage_imageι,
    Category.assoc, Scheme.Hom.toImage_imageι]
  exact h.symm

end

end ManuscriptAudit.SchematicImageIso

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SchematicImageIso.toImage_imageIso
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
