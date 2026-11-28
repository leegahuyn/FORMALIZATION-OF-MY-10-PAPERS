import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeCechNerve

/-! The actual Čech cochains are functorial on the opposite
of the ordinary category of actual site arrows. -/

namespace ManuscriptAudit.NativeCechArrowFunctor

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

private def nerveRightOp : (SimplicialObject C)ᵒᵖ ⥤ CosimplicialObject Cᵒᵖ where
  obj T := T.unop.rightOp
  map f := f.unop.rightOp
  map_id T := by
    change NatTrans.rightOp (𝟙 T.unop) = 𝟙 T.unop.rightOp
    exact NatTrans.rightOp_id
  map_comp f g := NatTrans.rightOp_comp g.unop f.unop

/-- Čech cochains of actual arrows and of actual presheaf sections. -/
def cochains (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (Arrow C)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{w} ℕ :=
  (SimplicialObject.cechNerve (C := C)).op ⋙ nerveRightOp ⋙
    (Functor.whiskeringRight SimplexCategory Cᵒᵖ AddCommGrpCat.{w}).obj P ⋙
    alternatingCofaceMapComplex _

/-- The functor uses the literal chosen nerve object at each degree. -/
theorem cochains_obj (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (f : Arrow C) :
    (cochains P).obj (op f) = NativeCechNerve.Cech f.hom P := rfl

/-- Restriction on a degree is the original site map on that nerve term. -/
theorem cochains_map_f (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {f g : Arrow C}
    (s : f ⟶ g) (n : ℕ) :
    ((cochains P).map s.op).f n = P.map ((Arrow.mapCechNerve s).app (op ⦋n⦌)).op :=
  rfl

end
end ManuscriptAudit.NativeCechArrowFunctor

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeCechArrowFunctor.cochains_map_f
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
