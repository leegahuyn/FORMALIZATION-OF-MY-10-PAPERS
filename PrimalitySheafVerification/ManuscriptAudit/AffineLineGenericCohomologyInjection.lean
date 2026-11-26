import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHTwo
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitCohomologyInjection
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-!
# Affine-line degree-two cohomology and the actual fraction field

The native divisor and first generic-point resolution sequences give
a degree-two injection into units on the fraction field. The verified
Kummer equivalence gives the corresponding injection for invertible
cyclic coefficients.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory
open GenericEtaleUnitSections KummerUnitsSheaf KummerCohomologyDegreeTwo

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K F : Type) [Field K] [IsAlgClosed K] [Field F]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]

private abbrev Y := Spec (CommRingCat.of F)

/-- The actual affine-line unit cohomology embeds in the fraction-field unit cohomology. -/
def affineLineUnitsHTwoEmbedding :
    {m : Sheaf.H (fullCoordinateUnitSheaf (X K)) 2 →+
        Sheaf.H (fullCoordinateUnitSheaf (Y F)) 2 // Function.Injective m} := by
  let e := genericImageHTwoEmbedding (Polynomial K) F
  let f := Sheaf.H.map (genericPointUnitsHom (Polynomial K) F) 2
  exact ⟨e.val.comp f, e.property.comp (regularUnits_HTwo_map_injective K F)⟩

/-- Degree-two cohomology for actual invertible cyclic coefficients on
the affine line embeds in fraction-field unit cohomology. -/
def affineLineCyclicHTwoEmbedding (d : ℕ) [NeZero (d : K)] :
    {m : Sheaf.H ((constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ZMod d))) 2 →+
        Sheaf.H (fullCoordinateUnitSheaf (Y F)) 2 // Function.Injective m} := by
  let e := affineLineCyclicHTwoFullUnitsEquiv K d
  let P := killedBy (Sheaf.H (fullCoordinateUnitSheaf (X K)) 2) d
  let r := affineLineUnitsHTwoEmbedding K F
  exact ⟨r.val.comp (P.subtype.comp e.toAddMonoidHom),
    r.property.comp (Subtype.val_injective.comp e.injective)⟩

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.affineLineUnitsHTwoEmbedding,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineLineCyclicHTwoEmbedding] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
