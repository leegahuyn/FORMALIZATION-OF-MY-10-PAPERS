import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination

/-!
# A good ordinary fiber at 7

The model from Paper 5 with fixed parameter `p_n = 7` and `A = 5`
has good reduction at 7. Its rational point group has order 7,
so its Frobenius trace is 1 and its rational points are 7-torsion.
-/

namespace ManuscriptAudit.Paper5OrdinarySeven

open WeierstrassCurve

noncomputable section

universe u

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def fixedCurve : WeierstrassCurve ℤ := ⟨0, 0, 0, -7, 5⟩

def ordinaryCurve (F : Type u) [Field F] : WeierstrassCurve F := ⟨0, 0, 0, 0, 5⟩

theorem fixedReduction_eq :
    fixedCurve.map (Int.castRingHom (ZMod 7)) = ordinaryCurve (ZMod 7) := by
  ext <;> decide

variable (F : Type u) [Field F]

abbrev Points := (ordinaryCurve F).toAffine.Point

theorem equation_iff (x y : F) :
    (ordinaryCurve F).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 5 := by
  rw [Affine.equation_iff]
  simp [ordinaryCurve]

variable [CharP F 7]

theorem seven_zero : (7 : F) = 0 := by
  simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero F 7)

theorem discriminant_eq_one : (ordinaryCurve F).Δ = 1 := by
  simp only [ordinaryCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (-1543 : F) * seven_zero F

instance ordinaryCurve_isElliptic : (ordinaryCurve F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, discriminant_eq_one F]
  exact isUnit_one

private abbrev Solutions := {xy : ZMod 7 × ZMod 7 // xy.2 ^ 2 = xy.1 ^ 3 + 5}

set_option maxRecDepth 12000 in
private theorem solutions_card : Fintype.card Solutions = 6 := by decide

theorem rational_affine_card : Nat.card (Points (ZMod 7)) = 7 := by
  let e : Points (ZMod 7) ≃ Option Solutions :=
    ((ordinaryCurve (ZMod 7)).toAffine.pointEquiv).trans
      (Equiv.subtypeEquivProp (fun xy => equation_iff (ZMod 7) xy.1 xy.2)).optionCongr
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option, solutions_card]

theorem rational_projective_card : Nat.card (ordinaryCurve (ZMod 7)).toProjective.Point = 7 := by
  rw [Nat.card_congr (Projective.Point.toAffineAddEquiv
    (W := (ordinaryCurve (ZMod 7)).toProjective)).toEquiv, rational_affine_card]

theorem rational_trace_one :
    (7 : ℤ) + 1 - Nat.card (ordinaryCurve (ZMod 7)).toProjective.Point = 1 := by
  rw [rational_projective_card]
  decide

theorem rational_point_is_seven_torsion (P : Points (ZMod 7)) : (7 : ℕ) • P = 0 := by
  rw [← rational_affine_card]
  exact card_nsmul_eq_zero'

theorem exists_nonzero_rational_seven_torsion :
    ∃ P : Points (ZMod 7), P ≠ 0 ∧ (7 : ℕ) • P = 0 := by
  have hEq : (ordinaryCurve (ZMod 7)).toAffine.Equation 3 2 :=
    (equation_iff (ZMod 7) 3 2).2 (by decide)
  refine ⟨Affine.Point.mk hEq, ?_, rational_point_is_seven_torsion _⟩
  change Affine.Point.some 3 2 _ ≠ Affine.Point.zero
  intro h
  cases h

end

end ManuscriptAudit.Paper5OrdinarySeven

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySeven.fixedReduction_eq,
      ``ManuscriptAudit.Paper5OrdinarySeven.discriminant_eq_one,
      ``ManuscriptAudit.Paper5OrdinarySeven.rational_affine_card,
      ``ManuscriptAudit.Paper5OrdinarySeven.rational_projective_card,
      ``ManuscriptAudit.Paper5OrdinarySeven.rational_trace_one,
      ``ManuscriptAudit.Paper5OrdinarySeven.rational_point_is_seven_torsion,
      ``ManuscriptAudit.Paper5OrdinarySeven.exists_nonzero_rational_seven_torsion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
