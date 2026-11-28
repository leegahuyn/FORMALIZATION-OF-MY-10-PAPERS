import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOnePicard
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineKummer
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffinePicard

/-!
# Actual first étale cohomology of the geometric affine elliptic curve

Finite roots-of-unity coefficients compute the genuine geometric point
torsion of the affine Weierstrass chart. The cyclic coefficient comparison
also holds after choosing the coefficient roots identification.
-/

namespace ManuscriptAudit.WeierstrassAffineHOneTorsion

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian WeierstrassCurve.Affine
open KummerCohomologyDegreeTwo TorsionFrobeniusModule

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

private def killedByToTorsion {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) : killedBy G d ≃+ Torsion d H where
  toFun u := ⟨e u.val, (mem_iff d H _).2 (by
    rw [← map_nsmul, show d • u.val = 0 from u.property, map_zero])⟩
  invFun v := ⟨e.symm v.val, by
    change d • e.symm v.val = 0
    rw [← map_nsmul, (mem_iff d H _).1 v.property, map_zero]⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' u v := Subtype.ext (e.map_add u.val v.val)

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev R := CommRingCat.of W.CoordinateRing

/-- Actual finite-degree full small étale roots-of-unity cohomology of the
geometric affine elliptic chart gives its genuine elliptic point torsion. -/
def rootsHOneEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (Spec (R W)).smallEtaleTopology AddCommGrpCat.{0}).obj
      (KummerConstantCoefficients.coefficientGroup K d)) 1 ≃+ Torsion d W.Point := by
  let e := (AffineEtaleHOnePicard.fullHOneEquiv W.CoordinateRing).trans
    (WeierstrassAffinePicard.pointPicardEquiv W).symm
  exact (WeierstrassAffineKummer.geometricRootsHOneEquiv W d).trans
    (killedByToTorsion e d)

/-- The actual full-site H¹ of the constant finite cyclic group has the same
underlying additive group as the genuine point torsion. -/
def cyclicHOneEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (Spec (R W)).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1 ≃+ Torsion d W.Point := by
  let e : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let s := (constantSheaf (Spec (R W)).smallEtaleTopology AddCommGrpCat.{0}).mapIso
    (e.toAddCommGrpIso : KummerConstantCoefficients.coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let h := ((Sheaf.functorH (Spec (R W)).smallEtaleTopology 1).mapIso s).addCommGroupIsoToAddEquiv
  exact h.symm.trans (rootsHOneEquiv W d)

end

end ManuscriptAudit.WeierstrassAffineHOneTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassAffineHOneTorsion.rootsHOneEquiv,
      ``ManuscriptAudit.WeierstrassAffineHOneTorsion.cyclicHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
