import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtalePointSections
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections

/-! The actual rational-section values agree across all opens containing
the generic point, and regular units evaluate by their true pullback. -/

namespace ManuscriptAudit.OpenEtaleGenericSectionValue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleTwoOpenHOne KummerUnitsSheaf GenericEtaleUnitSections

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Y X : Scheme.{0}} (f : Y ⟶ X)

private abbrev B := etaleBaseChange f
private abbrev T := identityObject Y

private def baseChangeTerminalIso (U : X.Etale) (h : IsTerminal ((B f).obj U)) :
    (B f).obj U ≅ T (Y := Y) :=
  h.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @Etale Y)

variable (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{0})
private abbrev D := (directImage f AddCommGrpCat.{0}).obj M

/-- A section on the actual direct image at an open whose base change
is terminal is exactly one native global section at the source. -/
def genericValue (U : X.Etale) (h : IsTerminal ((B f).obj U)) :
    (D f M).obj.obj (op U) ≃+ M.obj.obj (op (T (Y := Y))) :=
  (M.obj.mapIso (baseChangeTerminalIso f U h).symm.op).addCommGroupIsoToAddEquiv

/-- A map between terminal generic fibers transports their actual section
values, even when the two ambient base changes come from different sites. -/
theorem genericValue_transport {Z : Scheme.{0}} (g : Y ⟶ Z)
    (U : X.Etale) (V : Z.Etale)
    (hU : IsTerminal ((B f).obj U)) (hV : IsTerminal ((B g).obj V))
    (r : (B g).obj V ⟶ (B f).obj U) (x : (D f M).obj.obj (op U)) :
    genericValue g M V hV (M.obj.map r.op x) = genericValue f M U hU x := by
  let u := (baseChangeTerminalIso f U hU).inv
  let v := (baseChangeTerminalIso g V hV).inv
  have h : v ≫ r = u := hU.hom_ext _ _
  change M.obj.map v.op (M.obj.map r.op x) = M.obj.map u.op x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h]

/-- Restricting an actual generic section preserves its literal value. -/
theorem genericValue_natural {U V : X.Etale} (r : V ⟶ U)
    (hU : IsTerminal ((B f).obj U)) (hV : IsTerminal ((B f).obj V))
    (x : (D f M).obj.obj (op U)) :
    genericValue f M V hV ((D f M).obj.map r.op x) = genericValue f M U hU x := by
  let u := (baseChangeTerminalIso f U hU).inv
  let v := (baseChangeTerminalIso f V hV).inv
  have h : v ≫ (B f).map r = u := hU.hom_ext _ _
  change M.obj.map v.op (M.obj.map ((B f).map r).op x) = M.obj.map u.op x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h]

variable {U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (g : Y ⟶ U)

private theorem factoringProjection
    (hj : f = g ≫ j)
    (h : IsTerminal ((B f).obj (Scheme.Etale.mk j))) :
    (baseChangeTerminalIso f (Scheme.Etale.mk j) h).inv.left ≫ pullback.fst j f = g := by
  let t := (baseChangeTerminalIso f (Scheme.Etale.mk j) h).inv
  have ht : t.left ≫ pullback.snd j f = 𝟙 Y := MorphismProperty.Over.w t
  apply (cancel_mono j).mp
  rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  exact hj

/-- The genuine regular-to-generic unit morphism on a factoring open
is evaluated by the literal map from the generic scheme into that open. -/
theorem genericValue_regular (hj : f = g ≫ j)
    (h : IsTerminal ((B f).obj (Scheme.Etale.mk j)))
    (x : (fullCoordinateUnitSheaf X).obj.obj (op (Scheme.Etale.mk j))) :
    genericValue f (fullCoordinateUnitSheaf Y) (Scheme.Etale.mk j) h
      ((pullbackToDirectImage f).hom.app (op (Scheme.Etale.mk j)) x) =
      (ringUnits.map g.appTop) x := by
  let H := Scheme.Γ ⋙ ringUnits
  let t := (baseChangeTerminalIso f (Scheme.Etale.mk j) h).inv.left
  change H.map t.op (H.map (pullback.fst j f).op x) = H.map g.op x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, factoringProjection f j g hj h]

end

end ManuscriptAudit.OpenEtaleGenericSectionValue

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleGenericSectionValue.genericValue_transport,
      ``ManuscriptAudit.OpenEtaleGenericSectionValue.genericValue_natural,
      ``ManuscriptAudit.OpenEtaleGenericSectionValue.genericValue_regular] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
