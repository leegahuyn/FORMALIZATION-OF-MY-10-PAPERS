import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassArithmeticCoordinateFrobenius
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassSemilinearPointClass
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineDedekind
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffinePicard
import PrimalitySheafVerification.ManuscriptAudit.DedekindPicardRingIso

/-! The actual scalar extension of geometric affine Picard classes by
the arithmetic Frobenius is the true Frobenius on elliptic points. -/

namespace ManuscriptAudit.WeierstrassArithmeticPicardFrobenius

open Polynomial CommRing WeierstrassCurve.Affine
open CubicNonsplitFrobeniusTrace WeierstrassSemilinearPointClass
open WeierstrassArithmeticCoordinateFrobenius WeierstrassAffineDedekind
open WeierstrassAffinePicard DedekindClassMapIntegral
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]

private abbrev V {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := W.baseChange K
private abbrev R {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := (V K W).CoordinateRing

local instance : IsDedekindDomain (R K W) := coordinateRing_isDedekindDomain (V K W)

/-- Arithmetic Frobenius on the actual points of the geometric curve. -/
abbrev arithmeticPoint : (V K W).Point →+ (V K W).Point :=
  pointMapAt k K W (V K W) rfl (FiniteField.frobeniusAlgHom k K)

/-- True coordinate ring transport on ideal classes is the ordinary
arithmetic Frobenius point action under the actual point-class map. -/
theorem pointClass_frobenius (P : (V K W).Point) :
    ClassGroup.mulEquiv (coordinateFrobenius k K W) (Point.toClass P).toMul =
      (Point.toClass (arithmeticPoint k K W P)).toMul := by
  cases P with
  | zero =>
    change ClassGroup.mulEquiv (coordinateFrobenius k K W)
        (Point.toClass (0 : (V K W).Point)).toMul =
      (Point.toClass (arithmeticPoint k K W 0)).toMul
    rw [map_zero, Point.toClass_zero]
    exact (ClassGroup.mulEquiv (coordinateFrobenius k K W)).map_one
  | some x y h =>
    obtain ⟨h', hp⟩ := pointMapAt_some k K W (V K W) rfl
      (FiniteField.frobeniusAlgHom k K) x y h
    change ClassGroup.mulEquiv (coordinateFrobenius k K W)
        (Point.toClass (Point.some x y h)).toMul =
      (Point.toClass (arithmeticPoint k K W (Point.some x y h))).toMul
    rw [hp, classSome, classSome, class_mk0_map]
    apply congrArg (ClassGroup.mk0 : (Ideal (R K W))⁰ → _)
    apply Subtype.ext
    exact coordinateFrobenius_pointIdeal k K W x y

/-- The actual Picard base-change map of affine Frobenius intertwines
the canonical point–Picard isomorphism and true point Frobenius. -/
theorem pointPicard_frobenius (P : (V K W).Point) :
    letI : Algebra (R K W) (R K W) := DedekindPicardRingIso.algebra (coordinateFrobenius k K W)
    Pic.mapAlgebra (R K W) (R K W) (pointPicardEquiv (V K W) P).toMul =
      (pointPicardEquiv (V K W) (arithmeticPoint k K W P)).toMul := by
  let e := coordinateFrobenius k K W
  letI : Algebra (R K W) (R K W) := DedekindPicardRingIso.algebra e
  let c := (Point.toClass P).toMul
  change Pic.mapAlgebra (R K W) (R K W) (ClassGroup.equivPic (R K W) c) =
    ClassGroup.equivPic (R K W) (Point.toClass (arithmeticPoint k K W P)).toMul
  exact (DedekindPicardRingIso.equivPic_map e c).trans
    (congrArg (ClassGroup.equivPic (R K W)) (pointClass_frobenius k K W P))

end

end ManuscriptAudit.WeierstrassArithmeticPicardFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassArithmeticPicardFrobenius.pointClass_frobenius,
      ``ManuscriptAudit.WeierstrassArithmeticPicardFrobenius.pointPicard_frobenius] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
