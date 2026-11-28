import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOnePicard
import PrimalitySheafVerification.ManuscriptAudit.AffineKummerTateLimit
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffinePicard

/-! The actual geometric affine Kummer cohomology tower computes the native point Tate module. -/

namespace ManuscriptAudit.WeierstrassAffineKummerTate

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PowerTateModule

noncomputable section

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev R := CommRingCat.of W.CoordinateRing

/-- The compatible inverse limit of the genuine geometric affine Kummer-root
H¹ groups is the actual geometric point Tate module. -/
def affineRootsTateEquiv :
    ↥(AffineKummerTateLimit.compatible (R W) l) ≃+ Tate l W.Point := by
  have hUnit (n : ℕ) : IsUnit ((l ^ n : ℕ) : R W) := by
    have hk : IsUnit (l : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      (hk.pow n).map (algebraMap K W.CoordinateRing)
  have hPow (n : ℕ) : Function.Surjective (fun u : W.CoordinateRingˣ => u ^ (l ^ n)) :=
    WeierstrassAffineUnits.unit_power_surjective W (l ^ n) (pow_pos (Fact.out : l.Prime).pos n)
  let e := (KummerUnitsSheaf.unitCohomologyEquiv (R W) 1).trans
    ((AffineEtaleHOnePicard.fullHOneEquiv W.CoordinateRing).trans
      (WeierstrassAffinePicard.pointPicardEquiv W).symm)
  exact (AffineKummerTateLimit.tateEquiv (R W) l hUnit hPow).trans
    (mapAddEquiv l e).toAddEquiv

end

end ManuscriptAudit.WeierstrassAffineKummerTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassAffineKummerTate.affineRootsTateEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
