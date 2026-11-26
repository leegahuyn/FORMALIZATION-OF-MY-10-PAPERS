import Lean.Util.CollectAxioms
import Mathlib.Topology.Connected.TotallyDisconnected
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf

/-!
# Restriction of constant sections to a connected étale piece

The continuous-map presentation of the constant sheaf gives a
constant extension of each section from a preconnected, nonempty
overlap to either containing piece.
-/

namespace ManuscriptAudit.EtaleConstantRestriction

open AlgebraicGeometry CategoryTheory Opposite
open EtaleContinuousMapSheaf

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem constantRestriction_surjective {X : Scheme.{u}} {D U : X.Etale}
    (f : D ⟶ U) [PreconnectedSpace D.left] [Nonempty D.left]
    (M : AddCommGrpCat.{u}) :
    Function.Surjective (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M).obj.map
      f.op) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  let e := constantSheafContinuousMapIso X M
  let d : D.left := Classical.choice inferInstance
  intro a
  let a' : C(D.left, M) := e.hom.hom.app (op D) a
  let b : C(U.left, M) := ContinuousMap.const U.left (a' d)
  have hb : (continuousMapSheaf X M).obj.map f.op b = a' := by
    apply ContinuousMap.ext
    intro x
    change a' d = a' x
    exact TotallyDisconnectedSpace.eq_of_continuous a' a'.continuous d x
  refine ⟨e.inv.hom.app (op U) b, ?_⟩
  rw [← NatTrans.naturality_apply e.inv.hom f.op b, hb]
  exact congrArg (fun m => m.hom.app (op D) a) e.hom_inv_id

end

end ManuscriptAudit.EtaleConstantRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.EtaleConstantRestriction.constantRestriction_surjective
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
