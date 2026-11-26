import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedRecurrence

/-!
# Actual prime-field point counts for the Paper 5 table

The appendix uses A = 1. The actual projective point type is equivalent
to one point at infinity together with the modular affine solutions.
The count is certified for every printed row.
-/

namespace ManuscriptAudit.Paper5PrintedPointCounts

open PrimalitySheafVerification.ManuscriptAudit
open Paper5PrintedRecurrence
open scoped BigOperators

private abbrev residueEquation (p : ℕ) (x y : Fin p) : Prop :=
  y.val ^ 2 % p = (x.val ^ 3 + 1) % p

private abbrev residueSolutions (p : ℕ) :=
  {xy : Fin p × Fin p // residueEquation p xy.1 xy.2}

private theorem zmod_equation_iff_mod (p x y : ℕ) :
    (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + 1 ↔
      y ^ 2 % p = (x ^ 3 + 1) % p := by
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (ZMod.natCast_eq_natCast_iff' (y ^ 2) (x ^ 3 + 1) p)

private def affineResidueEquiv (p : ℕ) [NeZero p] :
    Paper5TraceAffine p (1 : ZMod p) ≃ residueSolutions p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨x, y⟩, h⟩
    refine ⟨(⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩), ?_⟩
    apply (zmod_equation_iff_mod p x.val y.val).mp
    simpa only [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, sub_zero] using h
  · rintro ⟨⟨x, y⟩, h⟩
    refine ⟨((x.val : ZMod p), (y.val : ZMod p)), ?_⟩
    simpa only [ZMod.natCast_self, zero_mul, sub_zero] using
      (zmod_equation_iff_mod p x.val y.val).mpr h
  · rintro ⟨⟨x, y⟩, h⟩
    exact Subtype.ext (Prod.ext (ZMod.natCast_zmod_val x) (ZMod.natCast_zmod_val y))
  · rintro ⟨⟨x, y⟩, h⟩
    exact Subtype.ext
      (Prod.ext (Fin.ext (ZMod.val_natCast_of_lt x.isLt)) (Fin.ext (ZMod.val_natCast_of_lt y.isLt)))

private def residueFibers (p : ℕ) :
    residueSolutions p ≃ Σ x : Fin p, {y : Fin p // residueEquation p x y} where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), xy.2.2⟩
  left_inv := by rintro ⟨⟨x, y⟩, h⟩; rfl
  right_inv := by rintro ⟨x, y, h⟩; rfl

private noncomputable def projectiveAffineEquiv {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    (paper5TraceCurve p (1 : ZMod p)).toProjective.Point ≃
      Option (Paper5TraceAffine p (1 : ZMod p)) := by
  let W := (paper5TraceCurve p (1 : ZMod p)).toProjective
  have hNonsing (x y : ZMod p) :
      W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 - (p : ZMod p) * x + 1 := by
    rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (paper5_traceCurve_discriminant_ne_zero hp (one_ne_zero : (1 : ZMod p) ≠ 0))]
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [W, paper5TraceCurve]
  let e₁ : W.Point ≃ W.toAffine.Point :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (W := W)).toEquiv
  let e₂ : W.toAffine.Point ≃ Option {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} :=
    W.toAffine.nonsingularPointEquiv
  let e₃ : {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} ≃
      Paper5TraceAffine p (1 : ZMod p) :=
    { toFun := fun xy => ⟨xy.1, (hNonsing _ _).mp xy.2⟩
      invFun := fun xy => ⟨xy.1, (hNonsing _ _).mpr xy.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact e₁.trans (e₂.trans e₃.optionCongr)

/-- The modular count, summed one first coordinate at a time. -/
def enumeratedPoints (p : ℕ) : ℕ :=
  (∑ x : Fin p, (Finset.univ.filter (residueEquation p x)).card) + 1

theorem projective_count_eq_enumerated {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (paper5TraceCurve p (1 : ZMod p)).toProjective.Point = enumeratedPoints p := by
  let e := (projectiveAffineEquiv hp).trans
    ((affineResidueEquiv p).trans (residueFibers p)).optionCongr
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sigma]
  simp only [enumeratedPoints, Fintype.card_subtype]

private def countedPoints (p : ℕ) : ℕ :=
  if p % 3 = 2 then p + 1 else enumeratedPoints p

private theorem projective_count_eq_counted {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (paper5TraceCurve p (1 : ZMod p)).toProjective.Point = countedPoints p := by
  unfold countedPoints
  split
  · rename_i h
    exact paper5_traceCurve_projective_count hp h one_ne_zero
  · exact projective_count_eq_enumerated hp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem printedRows_count_checks :
    printedRows.all (fun r => decide (5 ≤ r.prime ∧ countedPoints r.prime = r.points)) = true := by
  decide

/-- Every printed prime-field count is the cardinality of the actual projective point type. -/
theorem printedRows_actual_point_counts {r : Row} (hr : r ∈ printedRows) :
    Nat.card (paper5TraceCurve r.prime (1 : ZMod r.prime)).toProjective.Point = r.points := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  have hcheck : 5 ≤ r.prime ∧ countedPoints r.prime = r.points :=
    of_decide_eq_true (List.all_eq_true.mp printedRows_count_checks r hr)
  exact (projective_count_eq_counted hcheck.1).trans hcheck.2

/-- The first printed trace then agrees with the trace defined by the actual curve count. -/
theorem printedRows_actual_firstTrace {r : Row} (hr : r ∈ printedRows) :
    (r.prime : ℤ) + 1 - (Nat.card (paper5TraceCurve r.prime (1 : ZMod r.prime)).toProjective.Point : ℤ)
      = r.a1 := by
  rw [printedRows_actual_point_counts hr, printedRows_point_count_relation hr]
  ring

end ManuscriptAudit.Paper5PrintedPointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.Paper5PrintedPointCounts.projective_count_eq_enumerated,
        ``ManuscriptAudit.Paper5PrintedPointCounts.printedRows_actual_point_counts,
        ``ManuscriptAudit.Paper5PrintedPointCounts.printedRows_actual_firstTrace] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
