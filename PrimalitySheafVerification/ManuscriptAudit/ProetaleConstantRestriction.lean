import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant

/-! Constant sections extend from any nonempty preconnected native
pro-étale object to a containing object. -/

namespace ManuscriptAudit.ProetaleConstantRestriction

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleDiscreteConstant (constantIso)
open ProetaleResidueSheaves (continuousCoefficients)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}}

abbrev constant (X : Scheme.{0}) (M : Type) [AddCommGroup M] :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} M))

theorem constantRestriction_surjective {D U : X.ProEt} (f : D ⟶ U)
    [PreconnectedSpace D.left] [Nonempty D.left] (M : Type) [AddCommGroup M] :
    Function.Surjective ((constant X M).obj.map f.op) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  let F := (sheafCompose _ AddCommGrpCat.uliftFunctor.{1}).obj (continuousCoefficients X M)
  let e : constant X M ≅ F := constantIso X M
  let d : D.left := Classical.choice inferInstance
  intro a
  let a' : C(D.left, M) := (e.hom.hom.app (op D) a).down
  let b : F.obj.obj (op U) := ⟨ContinuousMap.const U.left (a' d)⟩
  have hb : F.obj.map f.op b = e.hom.hom.app (op D) a := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change a' d = a' x
    exact TotallyDisconnectedSpace.eq_of_continuous a' a'.continuous d x
  refine ⟨e.inv.hom.app (op U) b, ?_⟩
  rw [← NatTrans.naturality_apply e.inv.hom f.op b, hb]
  exact congrArg (fun m ↦ m.hom.app (op D) a) e.hom_inv_id

end
end ManuscriptAudit.ProetaleConstantRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleConstantRestriction.constantRestriction_surjective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
