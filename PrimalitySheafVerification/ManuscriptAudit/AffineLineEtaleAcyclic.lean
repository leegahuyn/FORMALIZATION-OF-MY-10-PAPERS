import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorFullExact
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHigher
import PrimalitySheafVerification.ManuscriptAudit.KummerCohomologyVanishing
import PrimalitySheafVerification.ManuscriptAudit.RatFuncGenericImageHigher
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-! Higher vanishing for the actual affine-line unit sheaf and constant cyclic sheaves. -/

namespace ManuscriptAudit.AffineLineEtaleAcyclic

open AlgebraicGeometry CategoryTheory AffineLineDivisorSheaf KummerUnitsSheaf

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

theorem units_H_succ_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (X K)) (n + 1)) := by
  cases n with
  | zero => exact KummerUnitsSheaf.unitHOne_subsingleton_of_pid (Polynomial K)
  | succ n =>
    exact SheafCohomologyVanishingLeft.H_succ_subsingleton
      (divisorSequence K (RatFunc K)) (divisorSequence_shortExact K (RatFunc K)) (n + 1)
      (divisor_H_succ_subsingleton K n)
      (RatFuncTsen.affineLine_genericUnitImage_H_succ_subsingleton K (n + 1))

theorem cyclic_H_succ_subsingleton (d : ℕ) [NeZero (d : K)] (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) (n + 1)) := by
  cases n with
  | zero => exact SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K d
  | succ n =>
    let k : X K ⟶ Spec (CommRingCat.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))
    exact KummerCohomologyVanishing.cyclic_H_succ_subsingleton k d (n + 1)
      (units_H_succ_subsingleton K n) (units_H_succ_subsingleton K (n + 1))

end
end ManuscriptAudit.AffineLineEtaleAcyclic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.AffineLineEtaleAcyclic.units_H_succ_subsingleton,
      ``ManuscriptAudit.AffineLineEtaleAcyclic.cyclic_H_succ_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
