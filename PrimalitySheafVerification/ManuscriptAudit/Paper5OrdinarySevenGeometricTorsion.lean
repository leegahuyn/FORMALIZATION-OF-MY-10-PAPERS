import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricScaling
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenOneTwist
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTorsion

/-! Every nonsingular centered curve in characteristic seven has seven geometric seven-torsion points. -/

namespace ManuscriptAudit.Paper5OrdinarySevenGeometricTorsion

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicGeometricScaling Paper5OrdinarySeven Paper5OrdinarySevenFrobenius
open Paper5OrdinarySevenOneTwist Paper5OrdinarySevenTorsion Paper5OrdinarySevenRotation

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def restrict {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) :
    {P : G // (7 : ℕ) • P = 0} ≃ {P : H // (7 : ℕ) • P = 0} where
  toFun P := ⟨e P, by rw [← map_nsmul, P.property, map_zero]⟩
  invFun P := ⟨e.symm P, by rw [← map_nsmul, P.property, map_zero]⟩
  left_inv P := Subtype.ext (e.symm_apply_apply P)
  right_inv P := Subtype.ext (e.apply_symm_apply P)

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]

/-- Actual geometric seven-torsion has exactly seven affine-model points for every nonzero A. -/
theorem affine_card (A : L) (hA : A ≠ 0) :
    Nat.card {P : (Curve A).Point // (7 : ℕ) • P = 0} = 7 := by
  let a := algebraMap (ZMod 7) L (5 : ZMod 7)
  have ha : a ≠ 0 := (map_ne_zero (algebraMap (ZMod 7) L)).mpr (by decide)
  let e₁ := Classical.choice
    (exists_scaleEquiv ha hA (disc L 5 (by decide))
      (shortCubic_discriminant_ne_zero Paper5OrdinarySevenSecant.two_ne (three_ne L) hA))
  let e : Points L ≃+ (Curve A).Point := (ordinaryEquiv L).trans e₁
  let Count (W : Affine L) := Nat.card {P : W.Point // (7 : ℕ) • P = 0} = 7
  have hBase : Count ((ordinaryCurve (ZMod 7)).toAffine.baseChange L) :=
    seven_torsion_cardinal L
  have hOrdinary : Count ((ordinaryCurve L).toAffine) :=
    Eq.mp (congrArg Count (ordinary_baseChange L)) hBase
  exact (Nat.card_congr (restrict e).symm).trans hOrdinary

theorem projective_card (A : L) (hA : A ≠ 0) :
    Nat.card {P : (shortCubic (0 : L) A).toProjective.Point // (7 : ℕ) • P = 0} = 7 := by
  let e : (shortCubic (0 : L) A).toProjective.Point ≃+ (Curve A).Point :=
    Projective.Point.toAffineAddEquiv ((shortCubic (0 : L) A).toProjective)
  exact (Nat.card_congr (restrict e)).trans (affine_card L A hA)

end
end ManuscriptAudit.Paper5OrdinarySevenGeometricTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenGeometricTorsion.affine_card,
      ``ManuscriptAudit.Paper5OrdinarySevenGeometricTorsion.projective_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
