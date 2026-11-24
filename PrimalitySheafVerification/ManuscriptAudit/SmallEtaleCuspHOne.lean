import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Full small étale H¹ of the affine line and the punctured cusp

The native affine computations transfer to the full small étale site
with the very same constant cyclic group.
-/

namespace ManuscriptAudit.SmallEtaleCuspHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open SmallEtaleCohomologyComparison

noncomputable section

attribute [local instance] fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev affineLine := CommRingCat.of (Polynomial K)
private abbrev puncturedCusp := CommRingCat.of (Localization.Away (CuspPunctured.cuspSquare K))
private abbrev cyclicGroup (d : ℕ) := AddCommGrpCat.of (ZMod d)

private abbrev cyclicHOne (R : CommRingCat.{0}) (d : ℕ) :=
  Sheaf.H ((constantSheaf (Spec R).smallEtaleTopology AddCommGrpCat.{0}).obj (cyclicGroup d)) 1

/-- On the full small étale site the affine line has trivial H¹ for these coefficients. -/
theorem affineLine_cyclic_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (cyclicHOne (affineLine K) d) := by
  let e := cohomologyEquiv (affineLine K) (cyclicGroup d) 1
  have h := AffineEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K d
  exact ⟨fun a b => e.symm.injective (h.elim _ _)⟩

/-- On the full small étale site the punctured cusp has H¹ isomorphic to
the cyclic coefficient group. -/
def puncturedCuspCyclicHOneEquiv (d : ℕ) [NeZero (d : K)] (hd : 2 ≤ d) :
    ZMod d ≃+ cyclicHOne (puncturedCusp K) d :=
  (AffineEtaleCuspHOne.cuspPuncturedCyclicHOneEquiv K d hd).trans
    (cohomologyEquiv (puncturedCusp K) (cyclicGroup d) 1)

end

end ManuscriptAudit.SmallEtaleCuspHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton,
      ``ManuscriptAudit.SmallEtaleCuspHOne.puncturedCuspCyclicHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
