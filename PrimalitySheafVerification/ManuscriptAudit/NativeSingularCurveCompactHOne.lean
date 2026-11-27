import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenClosedHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalRationalInfinity
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeConductorHOne

/-! Degree-one compact-support calculations for the actual affine
cusp, affine split node, and relative smooth open of the proper node. -/

namespace ManuscriptAudit.NativeSingularCurveCompactHOne

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension (extensionByZero)
open ProetaleConstantRestriction (constant)
open ProetaleOpenClosedHOne (compactConstantHOneEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
variable (d : ℕ) [NeZero (d : K)]

local instance cyclicTopology : TopologicalSpace (ZMod d) := ⊥
local instance cyclicDiscrete : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- Degree-one cohomology of native extension by zero of a cyclic constant sheaf. -/
abbrev compact {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] :=
  Sheaf.H ((extensionByZero j AddCommGrpCat.{1}).obj (constant U (ZMod d))) 1

private theorem range_of_complement {X : Type*} {U Z : Set X} (h : Uᶜ = Z) : U = Zᶜ := by
  rw [← h, compl_compl]

theorem cusp_affine_subsingleton :
    Subsingleton (compact d (CuspProperCompactification.affineOpen K)) := by
  letI := CuspRationalInfinity.infinityPoint_isClosedImmersion K
  let e := compactConstantHOneEquiv K (CuspRationalInfinity.infinityPoint K) (ZMod d)
    (CuspProperCompactification.affineOpen K)
    (range_of_complement (CuspInfinitySupport.affine_complement_eq_infinity K))
  letI := CuspNativeProetaleProperHOne.cyclic_HOne_subsingleton K d
  exact e.injective.subsingleton

def node_affine_equiv (h2 : (2 : K) ≠ 0) :
    compact d (NodalProjectiveClosure.affineOpen K) ≃+ ZMod d := by
  letI := NodalRationalInfinity.infinityPoint_isClosedImmersion K
  let e := compactConstantHOneEquiv K (NodalRationalInfinity.infinityPoint K) (ZMod d)
    (NodalProjectiveClosure.affineOpen K)
    (range_of_complement (NodalRationalInfinity.affine_complement_eq_infinity K))
  exact e.trans (NodalNativeConductorHOne.cyclicHOneEquiv K h2 d)

def node_smooth_equiv (h2 : (2 : K) ≠ 0) :
    compact d (NodalSmoothLocusOverlap.smoothOpen K).ι ≃+ ZMod d := by
  letI := NodalSmoothRationalBoundary.projectiveOrigin_closed K
  let e := compactConstantHOneEquiv K (NodalSmoothRationalBoundary.projectiveOrigin K) (ZMod d)
    (NodalSmoothLocusOverlap.smoothOpen K).ι (NodalSmoothRationalBoundary.smooth_range K)
  exact e.trans (NodalNativeConductorHOne.cyclicHOneEquiv K h2 d)

end
end ManuscriptAudit.NativeSingularCurveCompactHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeSingularCurveCompactHOne.cusp_affine_subsingleton,
      ``ManuscriptAudit.NativeSingularCurveCompactHOne.node_affine_equiv,
      ``ManuscriptAudit.NativeSingularCurveCompactHOne.node_smooth_equiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
