import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspChartIntersectionMaps
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleNestedOpenBoundary

/-! The actual punctured cusp has an injective finite cyclic class map in
native compact degree two. The second support comparison removes the cusp origin. -/

namespace ManuscriptAudit.CuspNativeCompactSmoothHTwoLower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspPunctured (cuspSquare)
open CuspProperCompactification (affineCusp affineOpen projectiveCusp)
open CuspProperYChart (lineOpen)
open CuspChartIntersection (overlapIsoLaurent)
open CuspChartIntersectionMaps (laurentToAffineCusp overlapIsoLaurent_inv_toAffineCusp)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspNativeCompactHTwoLower (affineFunctionsOverlapEquiv affineFunctionsConnecting_injective)
open CuspNativeCompactSmoothHOne (smoothOpen punctured_range properOrigin_closed)
open SmallEtaleGeometricBaseChange (cuspOrigin cuspOrigin_closedImmersion cuspPuncturedOpen)
open ProetaleContinuousDirectImageMaps (functionsOver)
open OpenProetaleExtension (extensionByZero restriction)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleMayerVietorisConnecting (connecting)
open ProetaleMayerVietorisSupport (connecting_injective_of_support)
open ProetaleNestedOpenBoundary (sequence sequence_shortExact smallerIso closedIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [IsAlgClosed F]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp F
private abbrev V := (cuspPuncturedOpen F).toScheme
private abbrev j := affineOpen F
private abbrev k := lineOpen F
private abbrev l := overlapOpen F
private abbrev i := (cuspPuncturedOpen F).ι
private abbrev o := cuspOrigin F

private theorem cuspSquare_not_mem_laurentMap (w : Spec (CommRingCat.of (LaurentPolynomial F))) :
    cuspSquare F ∉ (CuspYChartImage.laurentToCusp F w).asIdeal := by
  intro h
  change Polynomial.toLaurent ((Polynomial.X : Polynomial F) ^ 2) ∈ w.asIdeal at h
  have u : IsUnit (Polynomial.toLaurent ((Polynomial.X : Polynomial F) ^ 2)) := by
    rw [Polynomial.toLaurent_X_pow]
    exact LaurentPolynomial.isUnit_T _
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem w.asIdeal h u)

private theorem cuspSquare_not_mem_laurent (w : Spec (CommRingCat.of (LaurentPolynomial F))) :
    cuspSquare F ∉ (laurentToAffineCusp F w).asIdeal := by
  rw [laurentToAffineCusp, Scheme.Hom.comp_apply]
  exact cuspSquare_not_mem_laurentMap F _

theorem overlap_disjoint_origin :
    Disjoint (Set.range (l F)) (Set.range (o F ≫ j F)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨w, rfl⟩ ⟨b, hb⟩
  have hEq : pullback.fst (j F) (k F) w = o F b :=
    (j F).isOpenEmbedding.injective hb.symm
  have hAtOrigin : cuspSquare F ∈ (o F b).asIdeal := by
    change Polynomial.constantCoeff ((Polynomial.X : Polynomial F) ^ 2) ∈ b.asIdeal
    simp
  let e := overlapIsoLaurent F
  obtain ⟨a, ha⟩ := e.inv.surjective w
  rw [← ha] at hEq
  have ht := congrArg (fun f : Spec (CommRingCat.of (LaurentPolynomial F)) ⟶ affineCusp F ↦ f a)
    (overlapIsoLaurent_inv_toAffineCusp F)
  have hu : laurentToAffineCusp F a = o F b := ht.symm.trans hEq
  have hm : cuspSquare F ∈ (laurentToAffineCusp F a).asIdeal := by
    rw [hu]
    exact hAtOrigin
  exact cuspSquare_not_mem_laurent F a hm

variable (d : ℕ) [NeZero (d : F)]

local instance cyclicTopology : TopologicalSpace (ZMod d) := ⊥
local instance cyclicDiscrete : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev M := ZMod d

local instance : IsClosedImmersion (o F) := cuspOrigin_closedImmersion F
local instance : IsClosedImmersion (o F ≫ j F) := properOrigin_closed F

private abbrev S := sequence (j F) F (o F) (M d)

private theorem supportAway : IsZero ((restriction (l F) A).obj (S F d).X₃) :=
  (ProetaleDisjointClosedSupport.restriction_closed_isZero (o F ≫ j F) (l F) (M d)
    (overlap_disjoint_origin F)).of_iso ((restriction (l F) A).mapIso (closedIso (j F) F (o F) (M d)))

private def smoothOverlapEquiv :
    Sheaf.H ((restriction (l F) A).obj (S F d).X₁) 1 ≃+ ZMod d :=
  (ProetaleMayerVietorisSupport.overlapEquiv (j F) (k F) (l F) (fstLeg F) (sndLeg F)
    (overlap F) (cover F) (sequence_shortExact (j F) F (o F) (M d)) (supportAway F d) 0).trans
    (affineFunctionsOverlapEquiv F d)

private def smoothSupportIso :
    (extensionByZero (smoothOpen F) A).obj (constant (V F) (M d)) ≅ (S F d).X₁ :=
  (extensionByZero (smoothOpen F) A).mapIso (ProetaleDiscreteConstant.constantIso (V F) (M d)) ≪≫
    smallerIso (i F) (j F) F (o F) (M d) (punctured_range F)

/-- The cyclic Laurent class in actual compact degree two of the punctured cusp. -/
def smoothInclusion :
    ZMod d →+ Sheaf.H ((extensionByZero (smoothOpen F) A).obj (constant (V F) (M d))) 2 :=
  (cohomologyIso (X := X F) (smoothSupportIso F d).symm 2).toAddMonoidHom.comp
    ((connecting (j F) (k F) (l F) (fstLeg F) (sndLeg F) (overlap F) (cover F)
      (S F d).X₁ 1).comp (smoothOverlapEquiv F d).symm.toAddMonoidHom)

theorem smoothInclusion_injective : Function.Injective (smoothInclusion F d) := by
  have hi := connecting_injective_of_support (j F) (k F) (l F) (fstLeg F) (sndLeg F)
    (overlap F) (cover F) (sequence_shortExact (j F) F (o F) (M d)) (supportAway F d) 0
    (affineFunctionsConnecting_injective F d)
  exact (cohomologyIso (X := X F) (smoothSupportIso F d).symm 2).injective.comp
    (hi.comp (smoothOverlapEquiv F d).symm.injective)

end
end ManuscriptAudit.CuspNativeCompactSmoothHTwoLower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeCompactSmoothHTwoLower.overlap_disjoint_origin,
      ``ManuscriptAudit.CuspNativeCompactSmoothHTwoLower.smoothInclusion,
      ``ManuscriptAudit.CuspNativeCompactSmoothHTwoLower.smoothInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
