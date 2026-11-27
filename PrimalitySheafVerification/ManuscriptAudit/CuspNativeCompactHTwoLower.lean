import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDisjointClosedSupport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisSupport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenClosedHOne

/-! The actual affine cusp has an injective finite cyclic class map in
native compact degree two, obtained from the Laurent overlap. -/

namespace ManuscriptAudit.CuspNativeCompactHTwoLower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (affineCusp affineOpen projectiveCusp)
open CuspProperYChart (lineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover restrictEquiv)
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedKernelLocalSupport (K inc)
open ProetaleClosedOpenRestriction (extensionFunctionsIsoKernel)
open ProetaleOpenClosedHOne (closedSequence_shortExact)
open OpenProetaleExtension (extensionByZero restriction)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleMayerVietorisConnecting (connecting connecting_injective)
open ProetaleMayerVietorisSupport (connecting_injective_of_support)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [IsAlgClosed F]
variable (d : ℕ) [NeZero (d : F)]

local instance cyclicTopology : TopologicalSpace (ZMod d) := ⊥
local instance cyclicDiscrete : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp F
private abbrev U := affineCusp F
private abbrev j := affineOpen F
private abbrev k := lineOpen F
private abbrev l := overlapOpen F
private abbrev z := infinityPoint F
private abbrev M := ZMod d

private theorem complement : Set.range (j F) = (Set.range (z F))ᶜ := by
  rw [← CuspInfinitySupport.affine_complement_eq_infinity F, compl_compl]

private theorem overlap_disjoint_infinity : Disjoint (Set.range (l F)) (Set.range (z F)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨w, rfl⟩ h
  have hm : (l F) w ∈ Set.range (j F) := ⟨pullback.fst (j F) (k F) w, rfl⟩
  rw [complement F] at hm
  exact hm h

private def extensionKernelIso :
    (extensionByZero (j F) A).obj (functions (M d) (U F)) ≅ K (z F) (M d) := by
  letI := infinityPoint_isClosedImmersion F
  exact extensionFunctionsIsoKernel (z F) (j F) (M d) (complement F)

private abbrev kernelSequence :=
  ShortComplex.mk (inc (z F) (M d)) (diagonal (M d) (z F))
    (kernel.condition (diagonal (M d) (z F)))

private def supportSequence :=
  ShortComplex.mk ((extensionKernelIso F d).hom ≫ inc (z F) (M d))
    (diagonal (M d) (z F)) (by rw [Category.assoc, kernel.condition, comp_zero])

private theorem supportSequence_shortExact : (supportSequence F d).ShortExact := by
  letI := infinityPoint_isClosedImmersion F
  let e : kernelSequence F d ≅ supportSequence F d :=
    ShortComplex.isoMk (extensionKernelIso F d).symm (Iso.refl _) (Iso.refl _)
      (by simp [supportSequence, Category.assoc]) (by simp [supportSequence])
  exact ShortComplex.shortExact_of_iso e (closedSequence_shortExact F (z F) (M d))

private theorem ambient_connecting_injective :
    Function.Injective (connecting (j F) (k F) (l F) (fstLeg F) (sndLeg F) (overlap F) (cover F)
      (functions (M d) (X F)) 1) := by
  letI := CuspNativeProetaleAffineHOne.cyclic_HOne_subsingleton F d
  letI := ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton F d
  let i := ProetaleDiscreteConstant.constantIso (X F) (M d)
  let a := cohomologyIso (X := U F) ((restriction (j F) A).mapIso i.symm) 1
  let b := cohomologyIso (X := Spec (CommRingCat.of (Polynomial F)))
    ((restriction (k F) A).mapIso i.symm) 1
  have hj := (a.trans (restrictEquiv F d (j F))).injective.subsingleton
  have hk := (b.trans (restrictEquiv F d (k F))).injective.subsingleton
  exact connecting_injective (j F) (k F) (l F) (fstLeg F) (sndLeg F) (overlap F) (cover F) _ 1 hj hk

private theorem supportAway :
    IsZero ((restriction (l F) A).obj (supportSequence F d).X₃) := by
  letI := infinityPoint_isClosedImmersion F
  exact ProetaleDisjointClosedSupport.restriction_closed_isZero (z F) (l F) (M d)
    (overlap_disjoint_infinity F)

def affineFunctionsOverlapEquiv :
    Sheaf.H ((restriction (l F) A).obj ((extensionByZero (j F) A).obj (functions (M d) (U F)))) 1
      ≃+ ZMod d :=
  (ProetaleMayerVietorisSupport.overlapEquiv (j F) (k F) (l F) (fstLeg F) (sndLeg F)
    (overlap F) (cover F) (supportSequence_shortExact F d) (supportAway F d) 0).trans
    ((cohomologyIso ((restriction (l F) A).mapIso
      (ProetaleDiscreteConstant.constantIso (X F) (M d)).symm) 1).trans
        (CuspNativeProetaleHTwoLower.overlapEquiv F d))

private abbrev extensionIso :=
  (extensionByZero (j F) A).mapIso (ProetaleDiscreteConstant.constantIso (U F) (M d))

theorem affineFunctionsConnecting_injective :
    Function.Injective (connecting (j F) (k F) (l F) (fstLeg F) (sndLeg F) (overlap F) (cover F)
      ((extensionByZero (j F) A).obj (functions (M d) (U F))) 1) :=
  connecting_injective_of_support (j F) (k F) (l F) (fstLeg F) (sndLeg F)
    (overlap F) (cover F) (supportSequence_shortExact F d) (supportAway F d) 0
    (ambient_connecting_injective F d)

/-- The cyclic Laurent class with the actual affine support in the proper cusp. -/
def affineInclusion :
    ZMod d →+ Sheaf.H ((extensionByZero (j F) A).obj (constant (U F) (M d))) 2 :=
  (cohomologyIso (X := X F) (extensionIso F d).symm 2).toAddMonoidHom.comp
    ((connecting (j F) (k F) (l F) (fstLeg F) (sndLeg F) (overlap F) (cover F)
      ((extensionByZero (j F) A).obj (functions (M d) (U F))) 1).comp
        (affineFunctionsOverlapEquiv F d).symm.toAddMonoidHom)

/-- The actual compact degree-two map is injective for every invertible cyclic order. -/
theorem affineInclusion_injective : Function.Injective (affineInclusion F d) := by
  exact (cohomologyIso (X := X F) (extensionIso F d).symm 2).injective.comp
    ((affineFunctionsConnecting_injective F d).comp (affineFunctionsOverlapEquiv F d).symm.injective)

end
end ManuscriptAudit.CuspNativeCompactHTwoLower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeCompactHTwoLower.affineFunctionsOverlapEquiv,
      ``ManuscriptAudit.CuspNativeCompactHTwoLower.affineFunctionsConnecting_injective,
      ``ManuscriptAudit.CuspNativeCompactHTwoLower.affineInclusion,
      ``ManuscriptAudit.CuspNativeCompactHTwoLower.affineInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
