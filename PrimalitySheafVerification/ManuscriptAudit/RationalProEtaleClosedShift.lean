import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.DerivedSheafShift
import PrimalitySheafVerification.ManuscriptAudit.ProEtDirectImage
import PrimalitySheafVerification.ManuscriptAudit.RationalProEtaleCoefficients

/-!
# A shifted closed point with nonzero rational hypercohomology

Paper 7, Proposition .43 on physical p. 275, asserts that finite
closed support of a bounded constructible complex implies vanishing
in every positive degree. The rational 2-adic sheaf pushed forward
from the actual residue point at 5 is nonzero in degree zero.
Putting it in degree one moves those sections to first hypercohomology.
-/

namespace ManuscriptAudit.RationalProEtaleClosedShift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open DerivedSheafShift ProEtDirectImage RationalProEtaleCoefficients

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev S := Spec (CommRingCat.of ℤ)
private abbrev Z := Spec (CommRingCat.of (ZMod 5))
private abbrev J := Scheme.ProEt.topology S
private abbrev A := AddCommGrpCat.{1}

local instance : HasDerivedCategory (Sheaf J A) := HasDerivedCategory.standard _
local instance : HasExt.{1} (Sheaf J A) := IsGrothendieckAbelian.hasExt _

/-- The actual closed rational residue point of Spec ℤ at 5. -/
def closedPoint : Z ⟶ S :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 5)))

theorem closedPoint_isClosedImmersion : IsClosedImmersion closedPoint :=
  IsClosedImmersion.spec_of_surjective ZMod.intCast_surjective

private def point : Z := (⊥ : PrimeSpectrum (ZMod 5))

/-- The closed fiber has exactly one underlying point. -/
theorem closedPoint_range : Set.range closedPoint = {closedPoint point} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact Set.mem_singleton_iff.mpr (congrArg closedPoint (Subsingleton.elim p point))
  · intro hx
    exact ⟨point, (Set.mem_singleton_iff.mp hx).symm⟩

private def residueSheaf : Sheaf (Scheme.ProEt.topology Z) A :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{1}).obj (rationalTwoAdicSheaf Z)

/-- The rational coefficient sheaf pushed forward from the residue point. -/
def closedPushforward : Sheaf J A := (directImage closedPoint A).obj residueSheaf

/-- Every weakly étale object disjoint from the point has zero sections. -/
theorem closedPushforward_sections_isZero_outside (U : S.ProEt)
    (h : Disjoint (Set.range U.hom) (Set.range closedPoint)) :
    IsZero (closedPushforward.obj.obj (op U)) := by
  letI : IsEmpty ((baseChange closedPoint).obj U).left := ⟨fun x => by
    have hw : U.hom (pullback.fst U.hom closedPoint x) =
        closedPoint (pullback.snd U.hom closedPoint x) := by
      change (pullback.fst U.hom closedPoint ≫ U.hom) x =
        (pullback.snd U.hom closedPoint ≫ closedPoint) x
      rw [pullback.condition]
    exact Set.disjoint_left.mp h ⟨_, rfl⟩ ⟨_, hw.symm⟩⟩
  exact directImage_eval_isZero_of_isEmpty closedPoint residueSheaf U

/-- The actual direct image has distinct global sections. -/
theorem closedPushforward_sections_not_subsingleton :
    ¬ Subsingleton (closedPushforward.obj.obj (op (terminalObject S))) := by
  let e := ((directImageTerminalSectionsIso closedPoint A).app residueSheaf).addCommGroupIsoToAddEquiv
  have hZ :
      ¬ Subsingleton ((rationalTwoAdicSheaf Z).obj.obj (op (terminalObject Z))) :=
    sections_not_subsingleton (terminalObject Z) point
  intro h
  apply hZ
  constructor
  intro a b
  have he := h.elim (e.symm (ULift.up a)) (e.symm (ULift.up b))
  exact congrArg ULift.down (e.symm.injective he)

/-- Nonzero first hypercohomology of the actual shifted rational closed point. -/
theorem paper7_shifted_closed_point_hyperH_one_nonzero :
    ¬ Subsingleton (hyperH J (degreeOne J closedPushforward) 1) :=
  degreeOne_hyperH_not_subsingleton J closedPushforward (terminalObjectIsTerminal S)
    closedPushforward_sections_not_subsingleton

end

end ManuscriptAudit.RationalProEtaleClosedShift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.RationalProEtaleClosedShift.closedPoint_isClosedImmersion,
      ``ManuscriptAudit.RationalProEtaleClosedShift.closedPoint_range,
      ``ManuscriptAudit.RationalProEtaleClosedShift.closedPushforward_sections_isZero_outside,
      ``ManuscriptAudit.RationalProEtaleClosedShift.closedPushforward_sections_not_subsingleton,
      ``ManuscriptAudit.RationalProEtaleClosedShift.paper7_shifted_closed_point_hyperH_one_nonzero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
