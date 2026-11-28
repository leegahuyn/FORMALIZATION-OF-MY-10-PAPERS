import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicHOneLimit
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveKummerTate

/-! After choosing coherent coefficient roots, the native geometric
untwisted first étale ℓ-adic cohomology is the point Tate module. -/

namespace ManuscriptAudit.WeierstrassProjectiveCyclicTate

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassProjectiveKummerTate PowerTateModule

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

/-- The inverse limit of the actual constant-coefficient small étale H¹
groups is additively identified with the true geometric point Tate module. -/
def cyclicTateEquiv :
    ↥(FullEtaleCyclicHOneLimit.compatible (projectiveScheme W) l) ≃+ Tate l W.Point :=
  (FullEtaleCyclicHOneLimit.rootsEquiv (projectiveScheme W) l (toBase W)).trans
    (projectiveRootsTateEquiv W l)

end

end ManuscriptAudit.WeierstrassProjectiveCyclicTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveCyclicTate.cyclicTateEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
