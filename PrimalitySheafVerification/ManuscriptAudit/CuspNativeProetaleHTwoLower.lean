import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentCyclicHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisConnecting

/-! The Laurent overlap provides genuine degree-two native classes on the
proper cusp, via its actual two-open Mayer–Vietoris connecting map. -/

namespace ManuscriptAudit.CuspNativeProetaleHTwoLower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspProperYChart (lineOpen affine_chart_cover)
open CuspChartIntersection (overlapIsoLaurent)
open ProetaleOpenLocalLifts (openObject openArrow)
open OpenProetaleExtension (restriction)
open ProetaleOpenRestriction (restrictionConstantIso)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleMayerVietorisConnecting (connecting connecting_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev W := pullback (j K) (k K)
private abbrev l : W K ⟶ X K := pullback.fst (j K) (k K) ≫ j K

private abbrev fstLeg : openObject (l K) ⟶ openObject (j K) :=
  MorphismProperty.Over.homMk (pullback.fst (j K) (k K)) (by
    change pullback.fst (j K) (k K) ≫ (𝟙 (affineCusp K) ≫ j K) = 𝟙 (W K) ≫ l K
    simp only [Category.id_comp] <;> rfl)

private abbrev sndLeg : openObject (l K) ⟶ openObject (k K) :=
  MorphismProperty.Over.homMk (pullback.snd (j K) (k K)) (by
    change pullback.snd (j K) (k K) ≫ (𝟙 (Spec (CommRingCat.of (Polynomial K))) ≫ k K) =
      𝟙 (W K) ≫ l K
    simpa only [Category.id_comp] using (pullback.condition (f := j K) (g := k K)).symm)

private theorem overlap :
    IsPullback (fstLeg K) (sndLeg K) (openArrow (j K)) (openArrow (k K)) :=
  ProetaleAffineTensor.underlying_isPullback (IsPullback.of_hasPullback (j K) (k K))

private theorem cover : Set.range (j K) ∪ Set.range (k K) = Set.univ :=
  congrArg (fun O : (X K).Opens ↦ (O : Set (X K))) (affine_chart_cover K)

variable (d : ℕ) [NeZero (d : K)]

local instance cyclicTopology : TopologicalSpace (ZMod d) := ⊥
local instance cyclicDiscrete : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev M := ZMod d

private def restrictEquiv {U : Scheme.{0}} (f : U ⟶ X K) [IsOpenImmersion f] :
    Sheaf.H ((restriction f A).obj (constant (X K) (M d))) 1 ≃+
      Sheaf.H (constant U (M d)) 1 :=
  cohomologyIso (X := U) ((restrictionConstantIso.{0} f).app (AddCommGrpCat.of (ULift.{1} (M d)))) 1

private def overlapEquiv :
    Sheaf.H ((restriction (l K) A).obj (constant (X K) (M d))) 1 ≃+ ZMod d := by
  let e := overlapIsoLaurent K
  let a := cohomologyIso (X := W K) (ProetaleDiscreteConstant.constantIso (W K) (M d)) 1
  let b := SchemeIsoProetaleCohomology.continuousCohomologyEquiv e (M d) 1
  let c := cohomologyIso (X := Spec (CommRingCat.of (LaurentPolynomial K)))
      (ProetaleDiscreteConstant.constantIso _ (M d)) 1
  exact (restrictEquiv K d (l K)).trans
    (a.trans (b.trans (c.symm.trans (ProetaleLaurentCyclicHOne.cyclicToHOne K d).symm)))

/-- The Kummer class of the Laurent parameter gives an additive map into actual native H². -/
def cyclicInclusion : ZMod d →+ Sheaf.H (constant (X K) (M d)) 2 :=
  (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (constant (X K) (M d)) 1).comp (overlapEquiv K d).symm.toAddMonoidHom

/-- This native degree-two class map is injective for every invertible cyclic order. -/
theorem cyclicInclusion_injective : Function.Injective (cyclicInclusion K d) := by
  letI := CuspNativeProetaleAffineHOne.cyclic_HOne_subsingleton K d
  letI := ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton K d
  have hj := (restrictEquiv K d (j K)).injective.subsingleton
  have hk := (restrictEquiv K d (k K)).injective.subsingleton
  exact (connecting_injective (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K)
    (cover K) (constant (X K) (M d)) 1 hj hk).comp (overlapEquiv K d).symm.injective

end
end ManuscriptAudit.CuspNativeProetaleHTwoLower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeProetaleHTwoLower.cyclicInclusion,
      ``ManuscriptAudit.CuspNativeProetaleHTwoLower.cyclicInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
