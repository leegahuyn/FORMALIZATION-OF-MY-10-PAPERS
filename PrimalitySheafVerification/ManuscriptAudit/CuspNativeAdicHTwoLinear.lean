import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentNativeAdicLinear
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestrictionCoefficientNaturality
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomologyNaturality

/-! The actual degree-two cusp class is linear for the continuous
adic scalar action on the native pro-étale cohomology group. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoLinear

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspChartIntersection (overlapIsoLaurent)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspNativeAdicHTwoLower (adicInclusion overlapEquiv restrictEquiv)
open NativeAdicScalarAction (adicModule scalarMap multiply multiply_continuous)
open OpenProetaleExtension (restriction)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleLaurentCompatibleHOne (laurent)
open ProetaleLaurentNativeAdicHOne (adicEquiv)
open ProetaleMayerVietorisConnecting (connecting)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev W := pullback (affineOpen K) (lineOpen K)
private abbrev l := overlapOpen K
private abbrev F := functions ℤ_[ℓ] (X K)
private abbrev O := Sheaf.H ((restriction (l K) A).obj (F K ℓ)) 1

local instance : Module ℤ_[ℓ] ((X K).EllAdicCohomology ℓ 2) := adicModule (X K) ℓ 2
local instance : Module ℤ_[ℓ] ((laurent K).EllAdicCohomology ℓ 1) := adicModule (laurent K) ℓ 1

private def toLaurent : O K ℓ ≃+ (laurent K).EllAdicCohomology ℓ 1 :=
  (restrictEquiv K ℓ (l K)).trans
    (SchemeIsoProetaleCohomology.adicCohomologyEquiv (overlapIsoLaurent K) ℓ 1)

private abbrev scaleOverlap (r : ℤ_[ℓ]) : O K ℓ →+ O K ℓ :=
  Sheaf.H.map ((restriction (l K) A).map (scalarMap (X K) ℓ r)) 1

set_option maxHeartbeats 2000000 in
private theorem toLaurent_scale (r : ℤ_[ℓ]) (x : O K ℓ) :
    toLaurent K ℓ (scaleOverlap K ℓ r x) =
      Sheaf.H.map (scalarMap (laurent K) ℓ r) 1 (toLaurent K ℓ x) := by
  let e := SchemeIsoProetaleCohomology.adicCohomologyEquiv (overlapIsoLaurent K) ℓ 1
  let y := restrictEquiv K ℓ (l K) x
  calc
    _ = e (Sheaf.H.map (scalarMap (W K) ℓ r) 1 y) :=
      congrArg e (ProetaleOpenRestrictionCoefficientNaturality.restrictionH_naturality
        (l K) (multiply ℓ r) (multiply_continuous ℓ r) 1 x)
    _ = _ := SchemeIsoProetaleCohomologyNaturality.continuousCohomologyEquiv_map
      (overlapIsoLaurent K) (multiply ℓ r) (multiply_continuous ℓ r) 1 y

private theorem toLaurent_label (a : ℤ_[ℓ]) :
    toLaurent K ℓ ((overlapEquiv K ℓ).symm a) = (adicEquiv K ℓ).symm a :=
  (toLaurent K ℓ).apply_symm_apply ((adicEquiv K ℓ).symm a)

private theorem overlap_label_smul (r a : ℤ_[ℓ]) :
    (overlapEquiv K ℓ).symm (r • a) =
      scaleOverlap K ℓ r ((overlapEquiv K ℓ).symm a) := by
  apply (toLaurent K ℓ).injective
  rw [toLaurent_label, toLaurent_scale, toLaurent_label]
  exact ProetaleLaurentNativeAdicLinear.coordinate_smul K ℓ r a

set_option maxHeartbeats 2400000 in
/-- The native Laurent boundary is an adic-linear inclusion
into the actual proper-cusp degree-two cohomology group. -/
def adicLinearInclusion : ℤ_[ℓ] →ₗ[ℤ_[ℓ]] ((X K).EllAdicCohomology ℓ 2) where
  toAddHom := adicInclusion K ℓ
  map_smul' r a := by
    let D := connecting (affineOpen K) (lineOpen K) (l K) (fstLeg K) (sndLeg K)
      (overlap K) (cover K) (F K ℓ) 1
    let x := (overlapEquiv K ℓ).symm a
    change D ((overlapEquiv K ℓ).symm (r • a)) =
      Sheaf.H.map (scalarMap (X K) ℓ r) 2 (D x)
    rw [overlap_label_smul]
    exact ProetaleMayerVietorisNaturality.connecting_naturality (affineOpen K) (lineOpen K) (l K)
      (fstLeg K) (sndLeg K) (overlap K) (cover K) (scalarMap (X K) ℓ r) 1 x

theorem adicLinearInclusion_injective : Function.Injective (adicLinearInclusion K ℓ) :=
  CuspNativeAdicHTwoLower.adicInclusion_injective K ℓ

end

end ManuscriptAudit.CuspNativeAdicHTwoLinear

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicLinearInclusion,
      ``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicLinearInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
