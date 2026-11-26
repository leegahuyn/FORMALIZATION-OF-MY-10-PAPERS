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

private abbrev residueEquation (p A : ℕ) (x y : Fin p) : Prop :=
  y.val ^ 2 % p = (x.val ^ 3 + A) % p

private abbrev residueSolutions (p A : ℕ) :=
  {xy : Fin p × Fin p // residueEquation p A xy.1 xy.2}

private theorem zmod_equation_iff_mod (p A x y : ℕ) :
    (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + (A : ZMod p) ↔
      y ^ 2 % p = (x ^ 3 + A) % p := by
  let f := Nat.castRingHom (ZMod p)
  change f y ^ 2 = f x ^ 3 + f A ↔ y ^ 2 % p = (x ^ 3 + A) % p
  rw [← map_pow f y 2, ← map_pow f x 3, ← map_add f]
  exact ZMod.natCast_eq_natCast_iff' (y ^ 2) (x ^ 3 + A) p

private def affineResidueEquiv (p A : ℕ) [NeZero p] :
    Paper5TraceAffine p (A : ZMod p) ≃ residueSolutions p A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨x, y⟩, h⟩
    refine ⟨(⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩), ?_⟩
    apply (zmod_equation_iff_mod p A x.val y.val).mp
    simpa only [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, sub_zero] using h
  · rintro ⟨⟨x, y⟩, h⟩
    refine ⟨((x.val : ZMod p), (y.val : ZMod p)), ?_⟩
    simpa only [ZMod.natCast_self, zero_mul, sub_zero] using
      (zmod_equation_iff_mod p A x.val y.val).mpr h
  · rintro ⟨⟨x, y⟩, h⟩
    exact Subtype.ext (Prod.ext (ZMod.natCast_zmod_val x) (ZMod.natCast_zmod_val y))
  · rintro ⟨⟨x, y⟩, h⟩
    exact Subtype.ext
      (Prod.ext (Fin.ext (ZMod.val_natCast_of_lt x.isLt)) (Fin.ext (ZMod.val_natCast_of_lt y.isLt)))

private def residueFibers (p A : ℕ) :
    residueSolutions p A ≃ Σ x : Fin p, {y : Fin p // residueEquation p A x y} where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), xy.2.2⟩
  left_inv := by rintro ⟨⟨x, y⟩, h⟩; rfl
  right_inv := by rintro ⟨x, y, h⟩; rfl

private noncomputable def projectiveAffineEquiv {p A : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hA : (A : ZMod p) ≠ 0) :
    (paper5TraceCurve p (A : ZMod p)).toProjective.Point ≃
      Option (Paper5TraceAffine p (A : ZMod p)) := by
  let W := (paper5TraceCurve p (A : ZMod p)).toProjective
  have hNonsing (x y : ZMod p) :
      W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 - (p : ZMod p) * x + (A : ZMod p) := by
    rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (paper5_traceCurve_discriminant_ne_zero hp hA)]
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [paper5TraceCurve]
  let e₁ : W.Point ≃ W.toAffine.Point :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (W := W)).toEquiv
  let e₂ : W.toAffine.Point ≃ Option {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} :=
    W.toAffine.nonsingularPointEquiv
  let e₃ : {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} ≃
      Paper5TraceAffine p (A : ZMod p) :=
    { toFun := fun xy => ⟨xy.1, (hNonsing _ _).mp xy.2⟩
      invFun := fun xy => ⟨xy.1, (hNonsing _ _).mpr xy.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact e₁.trans (e₂.trans e₃.optionCongr)

/-- The modular count with a given constant, summed one first coordinate at a time. -/
def enumeratedPointsFor (p A : ℕ) : ℕ :=
  (∑ x : Fin p, (Finset.univ.filter (residueEquation p A x)).card) + 1

theorem projective_count_eq_enumeratedFor {p A : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hA : (A : ZMod p) ≠ 0) :
    Nat.card (paper5TraceCurve p (A : ZMod p)).toProjective.Point = enumeratedPointsFor p A := by
  let e := (projectiveAffineEquiv hp hA).trans
    ((affineResidueEquiv p A).trans (residueFibers p A)).optionCongr
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sigma]
  simp only [enumeratedPointsFor, Fintype.card_subtype]

def enumeratedPoints (p : ℕ) : ℕ := enumeratedPointsFor p 1

theorem projective_count_eq_enumerated {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (paper5TraceCurve p (1 : ZMod p)).toProjective.Point = enumeratedPoints p := by
  simpa only [Nat.cast_one, enumeratedPoints] using
    (projective_count_eq_enumeratedFor hp (A := 1)
      (by simpa only [Nat.cast_one] using (one_ne_zero : (1 : ZMod p) ≠ 0)))

/-- Use the cube permutation count for primes congruent to two modulo three. -/
def countedPointsFor (p A : ℕ) : ℕ :=
  if p % 3 = 2 then p + 1 else enumeratedPointsFor p A

theorem projective_count_eq_countedFor {p A : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hA : (A : ZMod p) ≠ 0) :
    Nat.card (paper5TraceCurve p (A : ZMod p)).toProjective.Point = countedPointsFor p A := by
  unfold countedPointsFor
  split
  · rename_i h
    exact paper5_traceCurve_projective_count hp h hA
  · exact projective_count_eq_enumeratedFor hp hA

private def countedPoints (p : ℕ) : ℕ := countedPointsFor p 1

private theorem projective_count_eq_counted {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (paper5TraceCurve p (1 : ZMod p)).toProjective.Point = countedPoints p := by
  simpa only [Nat.cast_one, countedPoints] using
    (projective_count_eq_countedFor hp (A := 1)
      (by simpa only [Nat.cast_one] using (one_ne_zero : (1 : ZMod p) ≠ 0)))

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
      [``ManuscriptAudit.Paper5PrintedPointCounts.projective_count_eq_enumeratedFor,
        ``ManuscriptAudit.Paper5PrintedPointCounts.projective_count_eq_countedFor,
        ``ManuscriptAudit.Paper5PrintedPointCounts.projective_count_eq_enumerated,
        ``ManuscriptAudit.Paper5PrintedPointCounts.printedRows_actual_point_counts,
        ``ManuscriptAudit.Paper5PrintedPointCounts.printedRows_actual_firstTrace] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
