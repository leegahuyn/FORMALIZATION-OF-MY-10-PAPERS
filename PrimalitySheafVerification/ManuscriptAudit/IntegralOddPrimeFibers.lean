import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntPrimeResidueFiber
import PrimalitySheafVerification.ManuscriptAudit.SmoothLocusBaseIso
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspArithmeticBump
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalArithmeticBump

/-! The canonical scheme fibers of both actual integral curve models
at prime ideals of the integers, and their actual smooth opens. -/

namespace ManuscriptAudit.IntegralOddPrimeFibers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntPrimeResidueFiber (closedPoint residueSpecIso canonicalFiberIso canonicalFiberIso_over)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 7000

variable (p : ℕ) [Fact p.Prime]

private abbrev base := Spec (CommRingCat.of ℤ)
private abbrev residuePoint := base.fromSpecResidueField (closedPoint p)
abbrev residueBase := Spec (base.residueField (closedPoint p))

abbrev cuspFiber := pullback (residuePoint p) IntegralCuspNodalAffine.cuspToInt
abbrev nodalFiber := pullback (residuePoint p) (NodalIntegralGluing.toBase ℤ)

def cuspToResidue : cuspFiber p ⟶ residueBase p :=
  pullback.fst _ _

def nodeToResidue : nodalFiber p ⟶ residueBase p :=
  pullback.fst _ _

instance cusp_locallyOfFinitePresentation : LocallyOfFinitePresentation (cuspToResidue p) :=
  inferInstanceAs (LocallyOfFinitePresentation
    (pullback.fst (residuePoint p) IntegralCuspNodalAffine.cuspToInt))

instance node_locallyOfFinitePresentation : LocallyOfFinitePresentation (nodeToResidue p) := by
  letI : LocallyOfFinitePresentation (NodalIntegralGluing.toBase ℤ) :=
    NodalIntegralGluing.model_locallyOfFinitePresentation ℤ
  exact inferInstanceAs (LocallyOfFinitePresentation
    (pullback.fst (residuePoint p) (NodalIntegralGluing.toBase ℤ)))

/-- The canonical cusp fiber at (p) is the genuine computed cusp over ZMod p. -/
def cuspIso : cuspFiber p ≅ AffineCuspSmoothLocus.cusp (ZMod p) :=
  (canonicalFiberIso p IntegralCuspNodalAffine.cuspToInt).symm ≪≫
    IntegralCuspNodalAffine.cuspFiberIso (ZMod p)

/-- The canonical open is the same scheme as the computed punctured cusp. -/
def cuspSmoothIso :
    (cuspToResidue p).smoothLocus.toScheme ≅ AffineCuspSmoothLocus.punctured (ZMod p) :=
  (SmoothLocusBaseIso.iso
    (IntegralCuspArithmeticBump.fiberToBase (ZMod p)) (residueSpecIso p)
    (canonicalFiberIso p IntegralCuspNodalAffine.cuspToInt) (cuspToResidue p)
    (canonicalFiberIso_over p IntegralCuspNodalAffine.cuspToInt)).symm ≪≫
    IntegralCuspArithmeticBump.fiberSmoothIso (ZMod p)

/-- The canonical nodal fiber is the actual proper nodal cubic over ZMod p. -/
def nodeIso : nodalFiber p ≅ NodalProjectiveClosure.projectiveNode (ZMod p) :=
  (canonicalFiberIso p (NodalIntegralGluing.toBase ℤ)).symm ≪≫
    IntegralNodalArithmeticBump.fiberIso (ZMod p)

/-- The actual relative smooth open of the canonical nodal fiber. -/
def nodeSmoothIso :
    (nodeToResidue p).smoothLocus.toScheme ≅ NodalSmoothLocusOverlap.smoothScheme (ZMod p) :=
  (SmoothLocusBaseIso.iso
    (IntegralNodalArithmeticBump.fiberToBase (ZMod p)) (residueSpecIso p)
    (canonicalFiberIso p (NodalIntegralGluing.toBase ℤ)) (nodeToResidue p)
    (canonicalFiberIso_over p (NodalIntegralGluing.toBase ℤ))).symm ≪≫
    IntegralNodalArithmeticBump.smoothFiberIso (ZMod p)

/-- The actual canonical nodal fiber has a nonsmooth point. -/
theorem node_not_smooth : ¬ AlgebraicGeometry.Smooth (nodeToResidue p) := by
  intro h
  letI : AlgebraicGeometry.Smooth (nodeToResidue p) := h
  let e := canonicalFiberIso p (NodalIntegralGluing.toBase ℤ)
  let i := residueSpecIso p
  have ht : e.hom ≫ nodeToResidue p ≫ i.inv =
      IntegralNodalArithmeticBump.fiberToBase (ZMod p) := by
    rw [← Category.assoc]
    have h' : e.hom ≫ nodeToResidue p =
        IntegralNodalArithmeticBump.fiberToBase (ZMod p) ≫ i.hom :=
      canonicalFiberIso_over p (NodalIntegralGluing.toBase ℤ)
    rw [h', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hSmooth : AlgebraicGeometry.Smooth (e.hom ≫ nodeToResidue p ≫ i.inv) := inferInstance
  exact IntegralNodalArithmeticBump.fiber_not_smooth (ZMod p) (ht ▸ hSmooth)

end
end ManuscriptAudit.IntegralOddPrimeFibers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralOddPrimeFibers.cuspIso,
      ``ManuscriptAudit.IntegralOddPrimeFibers.cuspSmoothIso,
      ``ManuscriptAudit.IntegralOddPrimeFibers.nodeIso,
      ``ManuscriptAudit.IntegralOddPrimeFibers.nodeSmoothIso,
      ``ManuscriptAudit.IntegralOddPrimeFibers.node_not_smooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
