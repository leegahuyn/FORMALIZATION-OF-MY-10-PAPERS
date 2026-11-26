import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.IsAlgClosed.Basic
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusExtensionFixed

/-! The actual extension-field point count gives the trace of each geometric Frobenius power modulo two. -/

namespace ManuscriptAudit.WeierstrassFrobeniusExtensionTrace

open Polynomial WeierstrassCurve WeierstrassFrobeniusFixed WeierstrassFrobeniusExtensionFixed
open TwoTorsionFrobeniusModule WeierstrassFrobeniusTwoTorsionTrace FrobeniusModTwoLinear
open WeierstrassFrobeniusModTwo FrobeniusModTwoIteration

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [DecidableEq L]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [DecidableEq E]

theorem affine_trace_pow_eq_point_count (i : E →ₐ[ZMod p] L) (W : Affine (ZMod p))
    (h : Nat.card (geometricTwoTorsion p L W) = 4) :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L W)
      ((frobeniusOfCardFour p L W h).toLinearMap ^ Module.finrank (ZMod p) E) =
      (Nat.card (W.baseChange E).Point : ZMod 2) := by
  let V := geometricTwoTorsion p L W
  let n := Module.finrank (ZMod p) E
  let F : V ≃ₗ[ZMod 2] V := frobeniusOfCardFour p L W h
  letI : Finite V := Nat.finite_of_card_ne_zero (by rw [show Nat.card V = 4 from h]; decide)
  let b : Module.Basis (Fin 2) (ZMod 2) V := basisOfCardFour V h
  have hinj : Function.Injective ⇑(F.toLinearMap ^ n) := by
    rw [Module.End.coe_pow]
    exact F.injective.iterate n
  let G : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (F.toLinearMap ^ n) hinj.bijective_of_finite
  let j := Affine.Point.map (W' := W) i
  have hj : Function.Injective j := Affine.Point.map_injective (W' := W) i
  have hIter (v : V) :
      inclusion _ (G v) = ((⇑(frobeniusOnPoints p L W))^[n]) (inclusion _ v) :=
    point_iterate_inclusion p L W h n v
  have hFixed : (∃ v : V, v ≠ 0 ∧ G v = v) ↔
      ∃ Q : (W.baseChange E).Point, Q ≠ 0 ∧ (2 : ℕ) • Q = 0 := by
    constructor
    · rintro ⟨v, hv, hvF⟩
      have hfixed := (hIter v).symm.trans (congrArg (inclusion _) hvF)
      obtain ⟨Q, hQ⟩ :=
        (point_iterate_eq_self_iff p L E i W (inclusion _ v)).mp hfixed
      change j Q = inclusion _ v at hQ
      refine ⟨Q, ?_, ?_⟩
      · intro h0
        apply hv
        apply inclusion_injective
        rw [map_zero, ← hQ, h0, map_zero]
      · apply hj
        rw [map_nsmul, map_zero, hQ]
        exact (in_image_iff _ _).mp ⟨v, rfl⟩
    · rintro ⟨Q, hQ, h2Q⟩
      have ht : (2 : ℕ) • j Q = 0 := by rw [← map_nsmul, h2Q, map_zero]
      obtain ⟨v, hv⟩ := (in_image_iff _ _).mpr ht
      refine ⟨v, ?_, ?_⟩
      · intro h0
        apply hQ
        apply hj
        rw [map_zero, ← hv, h0, map_zero]
      · apply inclusion_injective
        rw [hIter, hv]
        exact (point_iterate_eq_self_iff p L E i W _).mpr ⟨Q, rfl⟩
  let W₀ := W.baseChange E
  letI : Finite (WithZero {xy : E × E // W₀.Nonsingular xy.1 xy.2}) := by
    change Finite (Option {xy : E × E // W₀.Nonsingular xy.1 xy.2})
    infer_instance
  letI : Finite W₀.Point := Finite.of_injective _ (Affine.nonsingularPointEquiv W₀).injective
  change LinearMap.trace (ZMod 2) V G.toLinearMap = _
  apply scalar_eq_of_zero_iff
  rw [ZMod.natCast_eq_zero_iff, trace_zero_iff_nonzero_fixed V b G, hFixed,
    two_dvd_card_iff_nonzero_two_torsion]

theorem projective_trace_pow_eq_signed_point_count (i : E →ₐ[ZMod p] L)
    (W : Projective (ZMod p)) (h : Nat.card (geometricTwoTorsion p L W.toAffine) = 4)
    (hpTwo : p ≠ 2) :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L W.toAffine)
      ((frobeniusOfCardFour p L W.toAffine h).toLinearMap ^ Module.finrank (ZMod p) E) =
      (((Fintype.card E : ℤ) + 1 - (Nat.card (W.baseChange E).Point : ℤ)) : ZMod 2) := by
  have hcounts : Nat.card (W.toAffine.baseChange E).Point = Nat.card (W.baseChange E).Point :=
    Nat.card_congr (Projective.Point.toAffineAddEquiv (W := W.baseChange E)).symm.toEquiv
  rw [affine_trace_pow_eq_point_count p L E i W.toAffine h, hcounts]
  have hp : (p : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr ((Fact.out : p.Prime).odd_of_ne_two hpTwo)
  have hcard : (Fintype.card E : ZMod 2) = 1 := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, Nat.cast_pow, hp, one_pow]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one, hcard]
  rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_sub, neg_scalar_eq_self]

/-- Choosing a finite-field embedding is unnecessary if the geometric field is algebraically closed. -/
theorem projective_trace_pow_eq_signed_point_count_of_isAlgClosed [IsAlgClosed L]
    (W : Projective (ZMod p)) (h : Nat.card (geometricTwoTorsion p L W.toAffine) = 4)
    (hpTwo : p ≠ 2) :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L W.toAffine)
      ((frobeniusOfCardFour p L W.toAffine h).toLinearMap ^ Module.finrank (ZMod p) E) =
      (((Fintype.card E : ℤ) + 1 - (Nat.card (W.baseChange E).Point : ℤ)) : ZMod 2) := by
  letI : Algebra.IsAlgebraic (ZMod p) E := ⟨fun x => ⟨
    (Polynomial.X ^ Fintype.card E - Polynomial.X : (ZMod p)[X]),
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card,
    by simp [FiniteField.pow_card]⟩⟩
  exact projective_trace_pow_eq_signed_point_count p L E (IsAlgClosed.lift : E →ₐ[ZMod p] L)
    W h hpTwo

end
end ManuscriptAudit.WeierstrassFrobeniusExtensionTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionTrace.affine_trace_pow_eq_point_count,
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionTrace.projective_trace_pow_eq_signed_point_count,
      ``ManuscriptAudit.WeierstrassFrobeniusExtensionTrace.projective_trace_pow_eq_signed_point_count_of_isAlgClosed] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
