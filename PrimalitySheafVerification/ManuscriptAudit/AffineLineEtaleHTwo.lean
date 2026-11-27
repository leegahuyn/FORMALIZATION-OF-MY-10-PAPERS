import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineGenericCohomologyInjection
import PrimalitySheafVerification.ManuscriptAudit.RatFuncEtaleUnitsHTwo

/-! The actual étale degree-two cyclic cohomology of the affine line
vanishes over an algebraically closed field. -/

namespace ManuscriptAudit.AffineLineEtaleHTwo

open AlgebraicGeometry CategoryTheory KummerUnitsSheaf

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev X := Spec (CommRingCat.of (Polynomial K))

/-- Étale cyclic H² embeds in the vanishing unit H² of the rational function field. -/
theorem cyclic_HTwo_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H
      ((constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ZMod d))) 2) := by
  letI := RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton K
  exact (AffineLineDivisorSheaf.affineLineCyclicHTwoEmbedding K (RatFunc K) d).property.subsingleton

/-- Actual affine-line étale unit H² itself vanishes by the same generic injection. -/
theorem units_HTwo_subsingleton :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (X K)) 2) := by
  letI := RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton K
  exact (AffineLineDivisorSheaf.affineLineUnitsHTwoEmbedding K (RatFunc K)).property.subsingleton

end ManuscriptAudit.AffineLineEtaleHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineEtaleHTwo.cyclic_HTwo_subsingleton,
      ``ManuscriptAudit.AffineLineEtaleHTwo.units_HTwo_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
