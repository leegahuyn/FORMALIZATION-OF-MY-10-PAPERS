import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTwistGeometry

/-! All eighteen smooth characteristic-nineteen twists have nineteen geometric torsion points. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTwistTorsion

open WeierstrassCurve FiniteFieldPointCount
open Paper5OrdinaryNineteenCoordinates Paper5OrdinaryNineteenTorsionCard
open Paper5OrdinaryNineteenTwistGeometry
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

theorem projective_card (A : ZMod 19) (hA : A ≠ 0) :
    Nat.card {P : ((paper5TraceCurve 19 A).baseChange L).toProjective.Point // (19 : ℕ) • P = 0} = 19 := by
  rw [CubicGeometricTorsion.printed_cubic_baseChange_eq_zero]
  let W := (shortCubic (0 : L) (algebraMap (ZMod 19) L A)).toProjective
  let e : W.Point ≃+ Points L :=
    (Projective.Point.toAffineAddEquiv W).trans (exists_conjugacy L A hA).choose.symm
  let e' : {P : W.Point // (19 : ℕ) • P = 0} ≃ Torsion L :=
    { toFun := fun P => ⟨e P, by rw [← map_nsmul, P.property, map_zero]⟩
      invFun := fun P => ⟨e.symm P, by rw [← map_nsmul, P.property, map_zero]⟩
      left_inv := fun P => Subtype.ext (e.symm_apply_apply P)
      right_inv := fun P => Subtype.ext (e.apply_symm_apply P) }
  exact (Nat.card_congr e').trans (affine_card L)

end
end ManuscriptAudit.Paper5OrdinaryNineteenTwistTorsion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryNineteenTwistTorsion.projective_card
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
