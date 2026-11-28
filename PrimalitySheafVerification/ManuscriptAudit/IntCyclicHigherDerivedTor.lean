import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import PrimalitySheafVerification.ManuscriptAudit.IntCyclicProjectiveResolution
import PrimalitySheafVerification.ManuscriptAudit.IntegerResidueModuleIso

/-! Every native higher Tor group with a cyclic integer residue as the
resolved argument is zero in degrees at least two. -/

namespace ManuscriptAudit.IntCyclicHigherDerivedTor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open IntCyclicProjectiveResolution (residues resolution resolution_isZero_X_succ_succ)

noncomputable section

private abbrev C := ModuleCat.{0} ℤ

/-- The actual left-derived tensor with the quotient of the integers
vanishes in every degree at least two, for any first module. -/
theorem higher_quotient_isZero (A : C) (n k : ℕ) (hn : n ≠ 0) :
    IsZero (((Tor C (k + 2)).obj A).obj (residues n)) := by
  let F := (tensoringLeft C).obj A
  let P := resolution n hn
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F (k + 2))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _
    (F.map_isZero (resolution_isZero_X_succ_succ n hn k))

/-- The same vanishing is for the literal native residue module. -/
theorem higher_residue_isZero (A : C) (n k : ℕ) (hn : n ≠ 0) :
    IsZero (((Tor C (k + 2)).obj A).obj (ModuleCat.of ℤ (ZMod n))) :=
  IsZero.of_iso (higher_quotient_isZero A n k hn)
    ((((Tor C (k + 2)).obj A).mapIso (IntegerResidueModuleIso.quotientResidueIso n)).symm)

end
end ManuscriptAudit.IntCyclicHigherDerivedTor

open Lean Elab Command in
run_cmd do
  let names := [``ManuscriptAudit.IntCyclicHigherDerivedTor.higher_quotient_isZero,
    ``ManuscriptAudit.IntCyclicHigherDerivedTor.higher_residue_isZero]
  for name in names do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
