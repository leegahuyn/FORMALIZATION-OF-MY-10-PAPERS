import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Localization
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleNativePicardHOne
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassArithmeticPicardFrobenius

/-! The actual small-étale unit H¹ of the geometric affine chart maps
injectively and Frobenius-equivariantly to the true elliptic point group. -/

namespace ManuscriptAudit.WeierstrassArithmeticAffineHOnePoint

open AlgebraicGeometry CategoryTheory
open KummerUnitsSheaf OpenEtaleUnitHOneComposition AffineEtaleNativePicardHOne
open WeierstrassProjectiveClosure WeierstrassArithmeticFrobeniusScheme
open WeierstrassArithmeticCoordinateFrobenius WeierstrassArithmeticPicardFrobenius
open WeierstrassAffineDedekind WeierstrassAffinePicard

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private theorem open_of_eq {X U : Scheme.{0}} {f g : U ⟶ X}
    (h : f = g) [IsOpenImmersion g] : IsOpenImmersion f := by
  subst f
  infer_instance

private theorem pullback_congr {X U : Scheme.{0}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    unitPullback f = unitPullback g := by
  subst g
  rfl

private abbrev V {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := W.baseChange K
private abbrev R {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := (V K W).CoordinateRing

variable {k : Type} [Field k]
variable (K : Type) [Field K] [Algebra k K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]

private abbrev H {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := Sheaf.H (fullCoordinateUnitSheaf (affineScheme (V K W))) 1

/-- The actual affine étale unit cohomology class gives its native
Picard class and hence its unique geometric elliptic point. -/
def affineHOneToPoint : H K W →+ (V K W).Point :=
  (pointPicardEquiv (V K W)).symm.toAddMonoidHom.comp (nativePicardHOne (R K W))

theorem affineHOneToPoint_injective : Function.Injective (affineHOneToPoint K W) :=
  (pointPicardEquiv (V K W)).symm.injective.comp (nativePicardHOne_injective (R K W))

variable (k) [Fintype k]

/-- Under the genuine affine Picard map, actual scheme Frobenius acts
on the corresponding elliptic point by ordinary arithmetic Frobenius. -/
theorem affineHOneToPoint_frobenius (x : H K W) :
    affineHOneToPoint K W (unitPullback (affineFrobenius k K W).hom x) =
      arithmeticPoint k K W (affineHOneToPoint K W x) := by
  let T := R K W
  let e := coordinateFrobenius k K W
  let E := pointPicardEquiv (V K W)
  letI : IsDedekindDomain T := coordinateRing_isDedekindDomain (V K W)
  letI : Algebra T T := DedekindPicardRingIso.algebra e
  letI : IsLocalization (⊥ : Submonoid T) T := DedekindPicardRingIso.isLocalization e
  letI : Module.Flat T T := IsLocalization.flat T (⊥ : Submonoid T)
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap T T)) = (affineFrobenius k K W).hom :=
    spec_coordinateFrobenius k K W
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap T T))) := open_of_eq hspec
  have h := nativePicardHOne_pullback T T x
  rw [pullback_congr hspec] at h
  apply E.injective
  apply Additive.ext
  change (E (E.symm (nativePicardHOne T (unitPullback (affineFrobenius k K W).hom x)))).toMul =
    (E (arithmeticPoint k K W (E.symm (nativePicardHOne T x)))).toMul
  rw [E.apply_symm_apply]
  exact h.trans (by
    have hp := pointPicard_frobenius k K W (E.symm (nativePicardHOne T x))
    change CommRing.Pic.mapAlgebra T T (E (E.symm (nativePicardHOne T x))).toMul = _ at hp
    rw [E.apply_symm_apply] at hp
    exact hp)

end

end ManuscriptAudit.WeierstrassArithmeticAffineHOnePoint

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassArithmeticAffineHOnePoint.affineHOneToPoint_injective,
      ``ManuscriptAudit.WeierstrassArithmeticAffineHOnePoint.affineHOneToPoint_frobenius] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
