import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import PrimalitySheafVerification.ManuscriptAudit.TwoTorsionFrobeniusModule
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusModTwo

/-!
# Native Frobenius trace and determinant on a four-point two-torsion group

An actual count of four geometric two-torsion points supplies the
finite basis. The resulting mod-two trace is the signed arithmetic
point count, and the determinant is the prime reduced modulo two.
-/

namespace ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace

open WeierstrassCurve TwoTorsionFrobeniusModule FrobeniusModTwoLinear

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L]

abbrev geometricTwoTorsion (W : Affine (ZMod p)) := TwoTorsion (W.baseChange L).Point

variable (W : Affine (ZMod p))

private theorem finiteOfCardFour (h : Nat.card (geometricTwoTorsion p L W) = 4) :
    Finite (geometricTwoTorsion p L W) :=
  Nat.finite_of_card_ne_zero (by rw [h]; decide)

def frobeniusOfCardFour (h : Nat.card (geometricTwoTorsion p L W) = 4) :
    geometricTwoTorsion p L W ≃ₗ[ZMod 2] geometricTwoTorsion p L W :=
  letI := finiteOfCardFour p L W h
  frobeniusLinearEquiv p L W

theorem frobeniusOfCardFour_inclusion (h : Nat.card (geometricTwoTorsion p L W) = 4)
    (P : geometricTwoTorsion p L W) :
    inclusion _ (frobeniusOfCardFour p L W h P) =
      WeierstrassFrobeniusFixed.frobeniusOnPoints p L W (inclusion _ P) := rfl

theorem trace_eq_signed_affine_count (h : Nat.card (geometricTwoTorsion p L W) = 4)
    (hpTwo : p ≠ 2) :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L W)
      (frobeniusOfCardFour p L W h).toLinearMap =
        (((p : ℤ) + 1 - (Nat.card (W.baseChange (ZMod p)).Point : ℤ)) : ZMod 2) := by
  letI := finiteOfCardFour p L W h
  exact WeierstrassFrobeniusModTwo.trace_eq_signed_point_count_mod_two p L
    (geometricTwoTorsion p L W) W (frobeniusOfCardFour p L W h) (inclusion _)
    (inclusion_injective _) (in_image_iff _)
    (frobeniusOfCardFour_inclusion p L W h) (basisOfCardFour _ h) hpTwo

theorem det_eq_prime_cast (h : Nat.card (geometricTwoTorsion p L W) = 4)
    (hpTwo : p ≠ 2) :
    LinearMap.det (frobeniusOfCardFour p L W h).toLinearMap = (p : ZMod 2) :=
  (det_eq_one _ _).trans
    (ZMod.natCast_eq_one_iff_odd.mpr ((Fact.out : p.Prime).odd_of_ne_two hpTwo)).symm

theorem affine_count_eq_projective_count (W' : Projective (ZMod p)) :
    Nat.card (W'.toAffine.baseChange (ZMod p)).Point = Nat.card W'.Point := by
  have hW : W'.toAffine.baseChange (ZMod p) = W'.toAffine := by
    change W'.toAffine.map (RingHom.id (ZMod p)) = W'.toAffine
    exact WeierstrassCurve.map_id _
  rw [hW]
  exact Nat.card_congr (Projective.Point.toAffineAddEquiv (W := W')).symm.toEquiv

/-- The projective point count is the arithmetic input of the native mod-two representation. -/
theorem trace_eq_signed_projective_count (W' : Projective (ZMod p))
    (h : Nat.card (geometricTwoTorsion p L W'.toAffine) = 4) (hpTwo : p ≠ 2) :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L W'.toAffine)
      (frobeniusOfCardFour p L W'.toAffine h).toLinearMap =
        (((p : ℤ) + 1 - (Nat.card W'.Point : ℤ)) : ZMod 2) := by
  rw [trace_eq_signed_affine_count p L W'.toAffine h hpTwo,
    affine_count_eq_projective_count p W']

end

end ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace.frobeniusOfCardFour_inclusion,
      ``ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace.trace_eq_signed_affine_count,
      ``ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace.det_eq_prime_cast,
      ``ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace.trace_eq_signed_projective_count] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
