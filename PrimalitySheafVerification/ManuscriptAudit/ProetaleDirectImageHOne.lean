import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunction

/-! The actual degree-one comparison for pro-étale direct image is
injective for every scheme morphism and every abelian coefficient sheaf. -/

namespace ManuscriptAudit.ProetaleDirectImageHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleBaseChange (directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev A := AddCommGrpCat.{u + 1}
private abbrev C (Z : Scheme.{u}) := Sheaf (Scheme.ProEt.topology Z) A.{u}

local instance : EnoughInjectives (C Y) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1} (C := C Y)

private abbrev integers (Z : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology Z) A.{u}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private def constantIso : (inverseImage f).obj (integers Y) ≅ integers X :=
  (constantInverseImageIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The natural pro-étale degree-one map induced by inverse image and counit. -/
def comparison (F : C X) : Sheaf.H ((directImage f A.{u}).obj F) 1 →+ Sheaf.H F 1 :=
  ((Ext.mk₀ (constantIso f).inv).precomp F (zero_add 1)).comp
    (ExtOneAdjunction.map (adjunction f) (integers Y) F)

/-- The degree-one comparison is injective by the splitting criterion for Ext¹. -/
theorem comparison_injective (F : C X) : Function.Injective (comparison f F) := by
  have h : Function.LeftInverse
      ((Ext.mk₀ (constantIso f).hom).precomp F (zero_add 1))
      ((Ext.mk₀ (constantIso f).inv).precomp F (zero_add 1)) := by
    intro e
    change (Ext.mk₀ (constantIso f).hom).comp
      ((Ext.mk₀ (constantIso f).inv).comp e (zero_add 1)) (zero_add 1) = e
    rw [Ext.mk₀_comp_mk₀_assoc, (constantIso f).hom_inv_id, Ext.mk₀_id_comp]
  intro a b hab
  apply ExtOneAdjunction.map_injective (adjunction f) (integers Y) F
  apply h.injective
  exact hab

theorem directImage_HOne_subsingleton (F : C X) [Subsingleton (Sheaf.H F 1)] :
    Subsingleton (Sheaf.H ((directImage f A.{u}).obj F) 1) :=
  (comparison_injective f F).subsingleton

end
end ManuscriptAudit.ProetaleDirectImageHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleDirectImageHOne.comparison_injective,
      ``ManuscriptAudit.ProetaleDirectImageHOne.directImage_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
