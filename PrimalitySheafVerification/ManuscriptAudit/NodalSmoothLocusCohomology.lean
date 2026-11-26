import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoprimeTorusEtale
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusGm

/-! Ordinary étale H¹ of the actual smooth locus of the proper node is
the cyclic coefficient group over an algebraically closed field. -/

namespace ManuscriptAudit.NodalSmoothLocusCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalSmoothLocusOverlap (smoothScheme)
open NodalSmoothLocusGm (smoothLocusIsoGm)

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

/-- The ordinary geometric H¹ of the native smooth locus with prime-to-
characteristic cyclic coefficients. -/
def smoothLocusCyclicHOneEquiv (h2 : (2 : K) ≠ 0) (d : ℕ)
    [NeZero (d : K)] (hd : 2 ≤ d) :
    ZMod d ≃+ Sheaf.H ((constantSheaf (smoothScheme K).smallEtaleTopology
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 1 := by
  let h : (1 : ℕ).Coprime 1 := by decide
  let e := (CoprimeTorusEtale.curveIsoLaurent K h) ≪≫ (smoothLocusIsoGm K h2).symm
  exact (CoprimeTorusEtale.cyclicHOneEquiv K h d hd).trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv e (AddCommGrpCat.of (ZMod d)) 1)

end
end ManuscriptAudit.NodalSmoothLocusCohomology

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalSmoothLocusCohomology.smoothLocusCyclicHOneEquiv
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
