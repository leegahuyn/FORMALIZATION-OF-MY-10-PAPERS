import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusModTwoRecurrence
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusExtensionTrace

/-! The native characteristic polynomial of the actual Frobenius iterate over a finite field. -/

namespace ManuscriptAudit.WeierstrassFrobeniusExtensionCharpoly

open Polynomial WeierstrassCurve FrobeniusModTwoLinear
open WeierstrassFrobeniusTwoTorsionTrace WeierstrassFrobeniusExtensionTrace

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [DecidableEq E]

/-- The determinant of the true extension-field Frobenius is the field size reduced modulo two. -/
theorem projective_det_pow_eq_card (W : Projective (ZMod p))
    (h : Nat.card (geometricTwoTorsion p L W.toAffine) = 4) (hpTwo : p ≠ 2) :
    LinearMap.det
      ((frobeniusOfCardFour p L W.toAffine h).toLinearMap ^ Module.finrank (ZMod p) E) =
      (Fintype.card E : ZMod 2) := by
  rw [map_pow, det_eq_prime_cast p L W.toAffine h hpTwo,
    Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, Nat.cast_pow]

private theorem finiteModule (W : Projective (ZMod p))
    (h : Nat.card (geometricTwoTorsion p L W.toAffine) = 4) :
    Module.Finite (ZMod 2) (geometricTwoTorsion p L W.toAffine) := by
  letI : Finite (geometricTwoTorsion p L W.toAffine) :=
    Nat.finite_of_card_ne_zero (by rw [h]; decide)
  infer_instance

/-- The projective point trace and field size are the coefficients on actual geometric two-torsion. -/
theorem projective_charpoly_pow [IsAlgClosed L] (W : Projective (ZMod p))
    (h : Nat.card (geometricTwoTorsion p L W.toAffine) = 4) (hpTwo : p ≠ 2) :
    letI := finiteModule p L W h
    ((frobeniusOfCardFour p L W.toAffine h).toLinearMap ^ Module.finrank (ZMod p) E).charpoly =
      X ^ 2 - C (((Fintype.card E : ℤ) + 1 -
        (Nat.card (W.baseChange E).Point : ℤ)) : ZMod 2) * X + C (Fintype.card E : ZMod 2) := by
  let V := geometricTwoTorsion p L W.toAffine
  have hc : Nat.card V = 4 := h
  letI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  let b : Module.Basis (Fin 2) (ZMod 2) V := basisOfCardFour V hc
  letI : Module.Finite (ZMod 2) V := finiteModule p L W h
  let f : Module.End (ZMod 2) V :=
    (frobeniusOfCardFour p L W.toAffine h).toLinearMap ^ Module.finrank (ZMod p) E
  have hf : f.charpoly =
      X ^ 2 - C (LinearMap.trace (ZMod 2) V f) * X + C (LinearMap.det f) := by
    rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace (ZMod 2) b, LinearMap.det_toMatrix b]
  change f.charpoly = _
  rw [hf]
  rw [show LinearMap.trace (ZMod 2) V f = _ from
      projective_trace_pow_eq_signed_point_count_of_isAlgClosed p L E W h hpTwo,
    show LinearMap.det f = _ from projective_det_pow_eq_card p L E W h hpTwo]

end
end ManuscriptAudit.WeierstrassFrobeniusExtensionCharpoly

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionCharpoly.projective_det_pow_eq_card,
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionCharpoly.projective_charpoly_pow] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
