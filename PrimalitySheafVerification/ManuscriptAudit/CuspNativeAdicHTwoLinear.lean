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

private def toLaurent : O K ℓ ≃+ (laurent K).EllAdicCohomology ℓ 1 :=
  (restrictEquiv K ℓ (l K)).trans
    (SchemeIsoProetaleCohomology.adicCohomologyEquiv (overlapIsoLaurent K) ℓ 1)

private abbrev scaleOverlap (r : ℤ_[ℓ]) : O K ℓ →+ O K ℓ :=
  Sheaf.H.map ((restriction (l K) A).map (scalarMap (X K) ℓ r)) 1

set_option maxHeartbeats 600000 in
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

set_option maxHeartbeats 600000 in
private theorem overlap_label_mul (r a : ℤ_[ℓ]) :
    (overlapEquiv K ℓ).symm (r * a) =
      scaleOverlap K ℓ r ((overlapEquiv K ℓ).symm a) := by
  let x := (overlapEquiv K ℓ).symm a
  let T := toLaurent K ℓ
  let σ := Sheaf.H.map (scalarMap (laurent K) ℓ r) 1
  apply T.injective
  calc
    T ((overlapEquiv K ℓ).symm (r * a)) = (adicEquiv K ℓ).symm (r * a) :=
      toLaurent_label K ℓ (r * a)
    _ = σ ((adicEquiv K ℓ).symm a) :=
      ProetaleLaurentNativeAdicLinear.coordinate_smul K ℓ r a
    _ = σ (T x) := congrArg σ (toLaurent_label K ℓ a).symm
    _ = T (scaleOverlap K ℓ r x) := (toLaurent_scale K ℓ r x).symm

set_option maxHeartbeats 700000 in
theorem adicInclusion_map_mul (r a : ℤ_[ℓ]) :
    adicInclusion K ℓ (r * a) =
      Sheaf.H.map (scalarMap (X K) ℓ r) 2 (adicInclusion K ℓ a) := by
  let D := connecting (affineOpen K) (lineOpen K) (l K) (fstLeg K) (sndLeg K)
    (overlap K) (cover K) (F K ℓ) 1
  let x := (overlapEquiv K ℓ).symm a
  change D ((overlapEquiv K ℓ).symm (r * a)) =
    Sheaf.H.map (scalarMap (X K) ℓ r) 2 (D x)
  calc
    _ = D (scaleOverlap K ℓ r x) := congrArg D (overlap_label_mul K ℓ r a)
    _ = _ := ProetaleMayerVietorisNaturality.connecting_naturality (affineOpen K) (lineOpen K) (l K)
      (fstLeg K) (sndLeg K) (overlap K) (cover K) (scalarMap (X K) ℓ r) 1 x

local instance : Module ℤ_[ℓ] ((X K).EllAdicCohomology ℓ 2) := adicModule (X K) ℓ 2

/-- The native Laurent boundary is an adic-linear inclusion
into the actual proper-cusp degree-two cohomology group. -/
def adicLinearInclusion : ℤ_[ℓ] →ₗ[ℤ_[ℓ]] ((X K).EllAdicCohomology ℓ 2) where
  toAddHom := adicInclusion K ℓ
  map_smul' := adicInclusion_map_mul K ℓ

theorem adicLinearInclusion_injective : Function.Injective (adicLinearInclusion K ℓ) :=
  CuspNativeAdicHTwoLower.adicInclusion_injective K ℓ

end

end ManuscriptAudit.CuspNativeAdicHTwoLinear

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicInclusion_map_mul,
      ``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicLinearInclusion,
      ``ManuscriptAudit.CuspNativeAdicHTwoLinear.adicLinearInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
