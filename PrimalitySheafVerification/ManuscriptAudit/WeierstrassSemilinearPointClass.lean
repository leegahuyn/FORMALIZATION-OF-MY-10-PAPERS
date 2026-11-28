import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.DedekindClassMapIntegral
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassSemilinearCoordinate

/-! The native point-to-class construction preserves the literal
semilinear map on the finite points of an affine Weierstrass curve. -/

namespace ManuscriptAudit.WeierstrassSemilinearPointClass

open Polynomial WeierstrassCurve.Affine WeierstrassSemilinearCoordinate DedekindClassMapIntegral
open scoped nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [IsDedekindDomain W.CoordinateRing]

def pointIdeal {x y : K} (h : W.Nonsingular x y) : (Ideal W.CoordinateRing)⁰ :=
  ⟨CoordinateRing.XYIdeal W x (C y), mem_nonZeroDivisors_iff_ne_zero.mpr (by
    intro hI
    apply (CoordinateRing.XYIdeal' h).ne_zero
    rw [CoordinateRing.XYIdeal'_eq, hI] <;> rfl)⟩

theorem classSome {x y : K} (h : W.Nonsingular x y) :
    (Point.toClass (Point.some x y h)).toMul = ClassGroup.mk0 (pointIdeal W h) := by
  change ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) = _
  rw [← ClassGroup.mk_mk0 (K := W.FunctionField)]
  congr 1
  apply Units.ext
  rw [CoordinateRing.XYIdeal'_eq, FractionalIdeal.coe_mk0] <;> rfl

variable {L : Type*} [Field L] [DecidableEq L] (e : K ≃+* L)
variable [IsDedekindDomain (W.map e.toRingHom).CoordinateRing]

/-- Semilinear transport on the actual affine ideal class of a finite
point agrees with applying the field map to its coordinates. -/
theorem pointClass_some_natural {x y : K} (h : W.Nonsingular x y) :
    ClassGroup.mulEquiv (coordinateEquiv W e) (Point.toClass (Point.some x y h)).toMul =
      (Point.toClass (Point.some (e x) (e y) (h.map e.toRingHom))).toMul := by
  rw [classSome, classSome, class_mk0_map]
  apply congrArg (ClassGroup.mk0 : (Ideal (W.map e.toRingHom).CoordinateRing)⁰ → _)
  apply Subtype.ext
  exact coordinateEquiv_XYIdeal W e x y

end

end ManuscriptAudit.WeierstrassSemilinearPointClass

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassSemilinearPointClass.pointClass_some_natural
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
