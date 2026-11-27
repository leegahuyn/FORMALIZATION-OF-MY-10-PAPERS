import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedOpenRestriction

/-! The actual closed direct image vanishes on every disjoint open. -/

namespace ManuscriptAudit.ProetaleDisjointClosedSupport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension (restriction)
open ProetaleContinuousDirectImageMaps (functionsOver)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z Y : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : Y ⟶ X) [IsOpenImmersion j]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

private abbrev A := AddCommGrpCat.{1}

private theorem empty_closed_pullback (U : Y.ProEt) (hDisjoint : Disjoint (Set.range j) (Set.range i)) :
    IsEmpty (↥(pullback (U.hom ≫ j) i : Scheme.{0})) := by
  constructor
  intro x
  let a := pullback.fst (U.hom ≫ j) i x
  let b := pullback.snd (U.hom ≫ j) i x
  have h : j (U.hom a) = i b :=
    congrArg (fun f : pullback (U.hom ≫ j) i ⟶ X ↦ f x)
      (pullback.condition (f := U.hom ≫ j) (g := i))
  exact Set.disjoint_left.mp hDisjoint ⟨U.hom a, rfl⟩ ⟨b, h.symm⟩

theorem restriction_closed_isZero (hDisjoint : Disjoint (Set.range j) (Set.range i)) :
    IsZero ((restriction j A).obj (functionsOver M i)) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change ↥(pullback (U.unop.hom ≫ j) i : Scheme.{0}) at x
  exact ((empty_closed_pullback i j U.unop hDisjoint).false x).elim

end
end ManuscriptAudit.ProetaleDisjointClosedSupport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleDisjointClosedSupport.restriction_closed_isZero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
