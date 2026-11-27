import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTwistGeometry

/-! All twelve smooth characteristic-thirteen twists have thirteen geometric torsion points. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenTwistTorsion

open WeierstrassCurve FiniteFieldPointCount
open Paper5OrdinaryThirteenCoordinates Paper5OrdinaryThirteenTorsionCard
open Paper5OrdinaryThirteenTwistGeometry
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]

theorem projective_card (A : ZMod 13) (hA : A ≠ 0) :
    Nat.card {P : ((paper5TraceCurve 13 A).baseChange L).toProjective.Point // (13 : ℕ) • P = 0} = 13 := by
  rw [CubicGeometricTorsion.printed_cubic_baseChange_eq_zero]
  let W := (shortCubic (0 : L) (algebraMap (ZMod 13) L A)).toProjective
  let e : W.Point ≃+ Points L :=
    (Projective.Point.toAffineAddEquiv W).trans (exists_conjugacy L A hA).choose.symm
  let e' : {P : W.Point // (13 : ℕ) • P = 0} ≃ Torsion L :=
    { toFun := fun P => ⟨e P, by rw [← map_nsmul, P.property, map_zero]⟩
      invFun := fun P => ⟨e.symm P, by rw [← map_nsmul, P.property, map_zero]⟩
      left_inv := fun P => Subtype.ext (e.symm_apply_apply P)
      right_inv := fun P => Subtype.ext (e.apply_symm_apply P) }
  exact (Nat.card_congr e').trans (affine_card L)

end
end ManuscriptAudit.Paper5OrdinaryThirteenTwistTorsion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryThirteenTwistTorsion.projective_card
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
