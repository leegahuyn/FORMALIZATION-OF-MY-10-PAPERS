import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestrictionCoefficientNaturality
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoNativeAdicReduction

/-! The genuine native integral class of the proper cusp has the expected
nonzero finite residues, with all maps coming from actual coefficient reduction. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoReduction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspChartIntersection (overlapIsoLaurent)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspNativeAdicHTwoLower (adicInclusion overlapEquiv)
open OpenProetaleExtension (restriction)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleLaurentAdicCoordinates (levelEquiv compatibleEquiv_apply)
open ProetaleLaurentCompatibleHOne (laurent)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (reductionMap nativeCompatible)
open ProetaleMayerVietorisConnecting (connecting connecting_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev l := overlapOpen K
private abbrev W := pullback (j K) (k K)

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩
local instance cast_pow_neZero (n : ℕ) : NeZero ((ℓ ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩

private abbrev r (Y : Scheme.{0}) (n : ℕ) :=
  (ProetaleCoefficientUniverseLift.lift Y).map (ProetaleResidueSheaves.residueReduction Y ℓ n)

private def finiteOverlap (n : ℕ) :
    Sheaf.H ((restriction (l K) A).obj (finiteCoefficient (X K) ℓ n)) 1 ≃+
      Sheaf.H (finiteCoefficient (laurent K) ℓ n) 1 :=
  (cohomologyIso (X := W K) (restrictionFunctionsIso (l K) (ZMod (ℓ ^ n))) 1).trans
    (SchemeIsoProetaleCohomology.continuousCohomologyEquiv (overlapIsoLaurent K) (ZMod (ℓ ^ n)) 1)

private def integralOverlap :
    Sheaf.H ((restriction (l K) A).obj (functions ℤ_[ℓ] (X K))) 1 ≃+
      (laurent K).EllAdicCohomology ℓ 1 :=
  (CuspNativeAdicHTwoLower.restrictEquiv K ℓ (l K)).trans
    (SchemeIsoProetaleCohomology.adicCohomologyEquiv (overlapIsoLaurent K) ℓ 1)

set_option maxHeartbeats 2200000 in
private theorem overlap_reduction (n : ℕ)
    (x : Sheaf.H ((restriction (l K) A).obj (functions ℤ_[ℓ] (X K))) 1) :
    finiteOverlap K ℓ n (Sheaf.H.map ((restriction (l K) A).map (r ℓ (X K) n)) 1 x) =
      Sheaf.H.map (r ℓ (laurent K) n) 1 (integralOverlap K ℓ x) := by
  let d := (PadicInt.toZModPow n).toAddMonoidHom
  let hd := PadicResidueHomeomorphism.reduction_continuous ℓ n
  let e := SchemeIsoProetaleCohomology.continuousCohomologyEquiv (overlapIsoLaurent K) (ZMod (ℓ ^ n)) 1
  let y := CuspNativeAdicHTwoLower.restrictEquiv K ℓ (l K) x
  calc
    _ = e (Sheaf.H.map (r ℓ (W K) n) 1 y) :=
      congrArg e (ProetaleOpenRestrictionCoefficientNaturality.restrictionH_naturality (l K) d hd 1 x)
    _ = _ := SchemeIsoProetaleCohomologyNaturality.continuousCohomologyEquiv_map
      (overlapIsoLaurent K) d hd 1 y

private def overlapLabel (n : ℕ) :
    ZMod (ℓ ^ n) ≃+ Sheaf.H ((restriction (l K) A).obj (finiteCoefficient (X K) ℓ n)) 1 :=
  (levelEquiv K ℓ n).trans (finiteOverlap K ℓ n).symm

/-- The actual residue of the native Laurent class defines this finite class map. -/
def residueInclusion (n : ℕ) : ZMod (ℓ ^ n) →+ Sheaf.H (finiteCoefficient (X K) ℓ n) 2 :=
  (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (finiteCoefficient (X K) ℓ n) 1).comp (overlapLabel K ℓ n).toAddMonoidHom

theorem residueInclusion_injective (n : ℕ) : Function.Injective (residueInclusion K ℓ n) := by
  letI := CuspNativeProetaleAffineHOne.cyclic_HOne_subsingleton K (ℓ ^ n)
  letI := ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton K (ℓ ^ n)
  let d := ZMod (ℓ ^ n)
  let U := CuspProperCompactification.affineCusp K
  let V := Spec (CommRingCat.of (Polynomial K))
  let a := (cohomologyIso (X := U) (restrictionFunctionsIso (j K) d) 1).trans
    (cohomologyIso (X := U) (ProetaleDiscreteConstant.nativeResidueIso U ℓ n).symm 1)
  let b := (cohomologyIso (X := V) (restrictionFunctionsIso (k K) d) 1).trans
    (cohomologyIso (X := V) (ProetaleDiscreteConstant.nativeResidueIso V ℓ n).symm 1)
  exact (connecting_injective (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (finiteCoefficient (X K) ℓ n) 1 a.injective.subsingleton b.injective.subsingleton).comp
    (overlapLabel K ℓ n).injective

set_option maxHeartbeats 2400000 in
/-- The actual integral class reduces to the Laurent class at each finite level. -/
theorem reduction_adicInclusion (a : ℤ_[ℓ]) (n : ℕ) :
    (reductionMap (X K) ℓ 2 (adicInclusion K ℓ a)).val n =
      residueInclusion K ℓ n (PadicInt.toZModPow n a) := by
  let x := (overlapEquiv K ℓ).symm a
  let z := (ProetaleLaurentNativeAdicHOne.adicEquiv K ℓ).symm a
  have hx : integralOverlap K ℓ x = z :=
    (integralOverlap K ℓ).apply_symm_apply z
  have hz : Sheaf.H.map (r ℓ (laurent K) n) 1 z = levelEquiv K ℓ n (PadicInt.toZModPow n a) :=
    (congrArg (fun s : ProetaleAdicHOneDetection.compatibleHOne (laurent K) ℓ ↦ s.val n)
      (ProetaleLaurentNativeAdicHOne.adicEquiv_inverse_reduction K ℓ a)).trans
        (compatibleEquiv_apply K ℓ a n)
  let y := overlapLabel K ℓ n (PadicInt.toZModPow n a)
  have hy : Sheaf.H.map ((restriction (l K) A).map (r ℓ (X K) n)) 1 x = y := by
    apply (finiteOverlap K ℓ n).injective
    calc
      _ = Sheaf.H.map (r ℓ (laurent K) n) 1 (integralOverlap K ℓ x) :=
        overlap_reduction K ℓ n x
      _ = Sheaf.H.map (r ℓ (laurent K) n) 1 z := congrArg (Sheaf.H.map (r ℓ (laurent K) n) 1) hx
      _ = levelEquiv K ℓ n (PadicInt.toZModPow n a) := hz
      _ = _ := ((finiteOverlap K ℓ n).apply_symm_apply _).symm
  let D := connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (finiteCoefficient (X K) ℓ n) 1
  exact (ProetaleMayerVietorisNaturality.connecting_naturality (j K) (k K) (l K)
    (fstLeg K) (sndLeg K) (overlap K) (cover K) (r ℓ (X K) n) 1 x).symm.trans (congrArg D hy)

/-- The genuine reductions detect the whole exhibited copy of the adic integers. -/
theorem reduction_comp_injective :
    Function.Injective ((reductionMap (X K) ℓ 2).comp (adicInclusion K ℓ)) := by
  intro a b h
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  apply residueInclusion_injective K ℓ n
  have hn := congrArg (fun s : nativeCompatible (X K) ℓ 2 ↦ s.val n) h
  simpa only [AddMonoidHom.comp_apply, reduction_adicInclusion] using hn

end
end ManuscriptAudit.CuspNativeAdicHTwoReduction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoReduction.residueInclusion_injective,
      ``ManuscriptAudit.CuspNativeAdicHTwoReduction.reduction_adicInclusion,
      ``ManuscriptAudit.CuspNativeAdicHTwoReduction.reduction_comp_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
