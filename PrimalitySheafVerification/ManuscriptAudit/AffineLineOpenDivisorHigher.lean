import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineOpenDivisorCech
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-! The actual restricted divisor sheaf has no positive étale cohomology
on any affine open of the affine line. -/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory
open AffineEtaleCechSkyscrapers EtaleCechOrdinaryAcyclic EtaleObjectRestriction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]
variable (R : CommRingCat.{0}) (j : Spec R ⟶ X K) [IsOpenImmersion j]

private abbrev V := Spec R
private abbrev Ab := AddCommGrpCat.{0}
private abbrev E := Scheme.AffineEtale.sheafEquiv (V R) Ab

local instance : CategoryTheory.Limits.HasFiniteLimits (V R).AffineEtale :=
  AffineEtaleMorphism.spec_hasFiniteLimits R

/-- All positive ordinary cohomology of the actual divisor restriction
vanishes on the affine open, in particular on nonempty principal opens. -/
theorem restrictedDivisor_H_succ_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H ((restriction j).obj (divisorSheaf K)) (n + 1)) := by
  let A := (restriction j).obj (divisorSheaf K)
  let B := (affineOpenRestriction K R j).obj (affineDivisorSheaf K)
  have h := affine_H_succ_subsingleton (KummerAffineCohomology.affineTerminal_isTerminal R)
    (fun D _ ↦ exists_cechAcyclic_injectivePresentation R D) n B
    (affineRestrictedDivisor_cechAcyclic R K j)
  let e₀ := SmallEtaleCohomologyComparison.sheafCohomologyEquiv R B (n + 1)
  let e₁ := ((Sheaf.functorH (V R).smallEtaleTopology (n + 1)).mapIso
    ((E R).counitIso.app A)).addCommGroupIsoToAddEquiv
  let e := e₀.trans e₁
  exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.restrictedDivisor_H_succ_subsingleton
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
