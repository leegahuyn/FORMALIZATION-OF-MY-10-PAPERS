import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveUnitTate
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveKummer

/-! Actual first étale cohomology of the projective elliptic curve
with finite cyclic coefficients identifies with its geometric torsion. -/

namespace ManuscriptAudit.WeierstrassProjectiveHOneTorsion

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassProjectiveGenericQuotient
open WeierstrassProjectiveAffineExact WeierstrassProjectiveDegree
open WeierstrassInfinityMayerVietoris WeierstrassAffineOpenDivisorHOne
open KummerUnitsSheaf EtaleTerminalCohomology KummerCohomologyDegreeTwo TorsionFrobeniusModule

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev X := projectiveScheme W
private abbrev E := fullCoordinateUnitSheaf (X W)
private abbrev H := (E W).H' 1 (terminal W)
private abbrev A := (E W).H' 1 (Scheme.Etale.mk (affineOpen W))

private def killedByToTorsion {G P : Type} [AddCommGroup G] [AddCommGroup P]
    (e : G ≃+ P) (d : ℕ) : killedBy G d ≃+ Torsion d P where
  toFun u := ⟨e u.val, (mem_iff d P _).2 (by
    rw [← map_nsmul, show d • u.val = 0 from u.property, map_zero])⟩
  invFun v := ⟨e.symm v.val, by
    change d • e.symm v.val = 0
    rw [← map_nsmul, (mem_iff d P _).1 v.property, map_zero]⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' u v := Subtype.ext (e.map_add u.val v.val)

private def torsionOpenEquiv (d : ℕ) (hd : d ≠ 0) : Torsion d (H W) ≃+ Torsion d (A W) := by
  let hb := degree_boundary W
  let hn := neighborhoodMVRestriction_bijective W
  let he := affineRestriction_kernel W hn.1
  exact AddEquiv.ofBijective (mapAdd d (affineRestriction W))
    ⟨SplitIntegerBoundaryTorsion.torsion_injective _ _ he hb.injective d hd,
      SplitIntegerBoundaryTorsion.torsion_surjective _ _ he
        (affineRestriction_surjective W hn.2) (degree W) hb d⟩

private def torsionPointEquiv (d : ℕ) : Torsion d (A W) ≃+ Torsion d W.Point :=
  AddEquiv.ofBijective (mapAdd d (affineHOnePointEquiv W).toAddMonoidHom) (by
    constructor
    · intro x y h
      exact Subtype.ext ((affineHOnePointEquiv W).injective (congrArg Subtype.val h))
    · intro y
      let e := affineHOnePointEquiv W
      let x := e.symm y.val
      have hx : d • x = 0 := e.injective (by
        rw [map_nsmul, show e x = y.val from e.apply_symm_apply _, show d • y.val = 0 from y.property, map_zero])
      exact ⟨⟨x, hx⟩, Subtype.ext (e.apply_symm_apply _)⟩)

private def toPointTorsion (d : ℕ) (hd : d ≠ 0) :
    killedBy (Sheaf.H (E W) 1) d ≃+ Torsion d W.Point :=
  (killedByToTorsion (terminalHEquiv (X W) (E W) 1).symm d).trans
    ((torsionOpenEquiv W d hd).trans (torsionPointEquiv W d))

/-- Finite roots coefficients on the genuine projective curve give
exactly finite torsion in its native geometric point group. -/
def rootsHOnePointEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (X W).smallEtaleTopology AddCommGrpCat.{0}).obj
      (KummerConstantCoefficients.coefficientGroup K d)) 1 ≃+ Torsion d W.Point :=
  letI : NeZero d := NeZero.of_neZero_natCast K
  (WeierstrassProjectiveKummer.rootsHOneEquiv W d).trans (toPointTorsion W d (NeZero.ne d))

/-- The same native finite cohomology identifies with geometric point
torsion after choosing an identification of roots and cyclic coefficients. -/
def cyclicHOnePointEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (X W).smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1 ≃+ Torsion d W.Point :=
  letI : NeZero d := NeZero.of_neZero_natCast K
  (WeierstrassProjectiveKummer.cyclicHOneEquiv W d).trans (toPointTorsion W d (NeZero.ne d))

end

end ManuscriptAudit.WeierstrassProjectiveHOneTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveHOneTorsion.rootsHOnePointEquiv,
      ``ManuscriptAudit.WeierstrassProjectiveHOneTorsion.cyclicHOnePointEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
