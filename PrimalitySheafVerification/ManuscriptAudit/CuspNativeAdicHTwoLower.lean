import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentNativeAdicHOne

/-! The proper cusp has an additive copy of the adic integers in actual
integral native degree two, by its genuine Laurent Mayer–Vietoris class. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoLower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspChartIntersection (overlapIsoLaurent)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleCohomologyIso (cohomologyIso)
open OpenProetaleExtension (restriction)
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
private abbrev F := functions ℤ_[ℓ] (X K)

private def restrictEquiv {U : Scheme.{0}} (f : U ⟶ X K) [IsOpenImmersion f] :
    Sheaf.H ((restriction f A).obj (F K ℓ)) 1 ≃+ U.EllAdicCohomology ℓ 1 :=
  cohomologyIso (X := U) (restrictionFunctionsIso f ℤ_[ℓ]) 1

private def overlapEquiv :
    Sheaf.H ((restriction (l K) A).obj (F K ℓ)) 1 ≃+ ℤ_[ℓ] :=
  (restrictEquiv K ℓ (l K)).trans
    ((SchemeIsoProetaleCohomology.adicCohomologyEquiv (overlapIsoLaurent K) ℓ 1).trans
      (ProetaleLaurentNativeAdicHOne.adicEquiv K ℓ))

/-- The actual native Laurent class maps into the literal integral proper-cusp group. -/
def adicInclusion : ℤ_[ℓ] →+ (X K).EllAdicCohomology ℓ 2 :=
  (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (F K ℓ) 1).comp (overlapEquiv K ℓ).symm.toAddMonoidHom

theorem adicInclusion_injective : Function.Injective (adicInclusion K ℓ) := by
  letI := CuspNativeProetaleAffineHOne.adic_HOne_subsingleton K ℓ
  letI := ProetaleAffineLineAdicHOne.adic_HOne_subsingleton K ℓ
  have hj := (restrictEquiv K ℓ (j K)).injective.subsingleton
  have hk := (restrictEquiv K ℓ (k K)).injective.subsingleton
  exact (connecting_injective (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (F K ℓ) 1 hj hk).comp (overlapEquiv K ℓ).symm.injective

end
end ManuscriptAudit.CuspNativeAdicHTwoLower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoLower.adicInclusion,
      ``ManuscriptAudit.CuspNativeAdicHTwoLower.adicInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
