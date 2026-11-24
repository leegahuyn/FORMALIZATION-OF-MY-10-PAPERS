import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Sheaves.Skyscraper

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ManuscriptAudit.Paper07

universe u

/-- A cochain complex with its sole potentially nonzero term in degree one. -/
noncomputable def degreeOneSingle {R : Type u} [Ring R] (A : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 1).obj A

/-- The homology in degree one is the input module. -/
noncomputable def degreeOneSingleH1Iso {R : Type u} [Ring R] (A : ModuleCat.{u} R) :
    (degreeOneSingle A).homology 1 ≅ A :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 1 A

/-- A nonzero coefficient module gives nonzero degree-one cohomology. This
calculation holds for any nonzero module, including a field as its own module. -/
theorem degreeOneSingle_H1_nonzero {R : Type u} [Ring R] (A : ModuleCat.{u} R)
    (hA : ¬ IsZero A) : ¬ IsZero ((degreeOneSingle A).homology 1) := by
  intro hZero
  exact hA (hZero.of_iso (degreeOneSingleH1Iso A).symm)

/-- The degree-one shift has zero cohomology in every other degree. -/
theorem degreeOneSingle_other_H_zero {R : Type u} [Ring R] (A : ModuleCat.{u} R)
    (i : ℤ) (hi : i ≠ 1) : IsZero ((degreeOneSingle A).homology i) :=
  HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 1 A i hi

private abbrev F5Module := ModuleCat.of (ZMod 5) (ZMod 5)

/-- The actual topological skyscraper sheaf on a singleton, with coefficients
in the module `𝔽₅`. -/
noncomputable def pointSkyscraper :
    TopCat.Sheaf (ModuleCat (ZMod 5)) (TopCat.of PUnit) := by
  classical
  exact skyscraperSheaf (X := TopCat.of PUnit) PUnit.unit F5Module

/-- Evaluation on the whole singleton gives the skyscraper's value. -/
theorem pointSkyscraper_globalSections :
    pointSkyscraper.obj.obj (op (⊤ : Opens (TopCat.of PUnit))) = F5Module := by
  classical
  simp [pointSkyscraper, skyscraperSheaf, skyscraperPresheaf]

/-- The singleton global-sections calculation for the degree-one skyscraper.
Evaluation at the whole point is exact on a singleton, where a sheaf is
determined by its value on the whole space and its terminal value on the
empty open. The Lean definition uses evaluation of the actual skyscraper
followed by the single-cochain-complex construction. -/
noncomputable def pointSkyscraperSectionsComplex : CochainComplex (ModuleCat (ZMod 5)) ℤ :=
  degreeOneSingle (pointSkyscraper.obj.obj (op (⊤ : Opens (TopCat.of PUnit))))

/-- Paper 7, PDF p. 275, Proposition .43. The singleton global-sections
complex in degree one has nonzero degree-one homology. This formalizes the
shift calculation behind the counterexample. The manuscript's arithmetic
application uses a closed-point pushforward of a nonzero coefficient sheaf. -/
theorem page275_point_complex_H1_nonzero :
    ¬ IsZero (pointSkyscraperSectionsComplex.homology 1) := by
  rw [pointSkyscraperSectionsComplex, pointSkyscraper_globalSections]
  apply degreeOneSingle_H1_nonzero
  intro hZero
  have hSub : Subsingleton (ZMod 5) := ModuleCat.isZero_iff_subsingleton.mp hZero
  exact (by decide : (0 : ZMod 5) ≠ 1) (hSub.elim 0 1)

theorem page275_point_complex_other_H_zero (i : ℤ) (hi : i ≠ 1) :
    IsZero (pointSkyscraperSectionsComplex.homology i) :=
  degreeOneSingle_other_H_zero _ i hi

end ManuscriptAudit.Paper07

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.Paper07.degreeOneSingleH1Iso,
    ``ManuscriptAudit.Paper07.degreeOneSingle_H1_nonzero,
    ``ManuscriptAudit.Paper07.degreeOneSingle_other_H_zero,
    ``ManuscriptAudit.Paper07.pointSkyscraper_globalSections,
    ``ManuscriptAudit.Paper07.page275_point_complex_H1_nonzero,
    ``ManuscriptAudit.Paper07.page275_point_complex_other_H_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
