import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import PrimalitySheafVerification.ManuscriptAudit.CubicFiniteTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicTraceInfinitude
import PrimalitySheafVerification.ManuscriptAudit.EllipticFiniteDescent

/-!
# The geometric p-torsion of the printed reduced cubic

The finite-field calculation concerns the genuine projective group
law. Every point over an algebraic closure is already defined over a
finite field, and the injective point map reflects its torsion relation.
-/

namespace ManuscriptAudit.CubicGeometricTorsion

open WeierstrassCurve
open PrimalitySheafVerification.ManuscriptAudit
  (paper5TraceCurve paper5_arbitrarily_large_good_trace_zero)
open FiniteFieldPointCount (shortCubic)

private theorem printed_cubic_baseChange_eq_zero (p : ℕ) {L : Type*} [Field L]
    [Fact p.Prime] [Algebra (ZMod p) L] (A : ZMod p) :
    (paper5TraceCurve p A).baseChange L =
      shortCubic (0 : L) (algebraMap (ZMod p) L A) := by
  simp [paper5TraceCurve, shortCubic, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    ZMod.natCast_self]

private theorem finite_affine_no_p_torsion {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Fintype L] [Algebra (ZMod p) L] (hp : 5 ≤ p) (hr : p % 3 = 2)
    {A : ZMod p} (hA : A ≠ 0) :
    ∀ Q : ((paper5TraceCurve p A).baseChange L).toAffine.Point, p • Q = 0 → Q = 0 := by
  classical
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  rw [printed_cubic_baseChange_eq_zero p A]
  intro Q hQ
  let e := (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := (shortCubic (0 : L) (algebraMap (ZMod p) L A)).toProjective)).symm
  have hT : p • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  have hA' : algebraMap (ZMod p) L A ≠ 0 := by
    simpa only [map_zero] using (algebraMap (ZMod p) L).injective.ne hA
  have hzero := CubicFiniteTorsion.paper5_no_p_torsion_over_finite_field hp hr hA' (e Q) hT
  apply e.injective
  simpa only [map_zero] using hzero

/-- The printed reduction has trivial geometric p-torsion in every
algebraic extension of its residue field. -/
theorem paper5_no_geometric_p_torsion {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]
    (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (P : ((paper5TraceCurve p A).baseChange L).toProjective.Point)
    (hP : p • P = 0) : P = 0 := by
  classical
  let e := WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := ((paper5TraceCurve p A).baseChange L).toProjective)
  apply e.injective
  rw [map_zero]
  refine EllipticFiniteDescent.torsion_eq_zero_of_finite_fields
    (paper5TraceCurve p A).toAffine p ?_ (e P) ?_
  · intro E hE
    letI : Finite E := hE
    letI := Fintype.ofFinite E
    exact finite_affine_no_p_torsion (L := E) hp hr hA
  · rw [← map_nsmul, hP, map_zero]

/-- In particular, the usual geometric p-torsion group over the algebraic
closure consists only of the identity. -/
theorem paper5_no_p_torsion_over_algebraicClosure {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point)
    (hP : p • P = 0) : P = 0 :=
  paper5_no_geometric_p_torsion hp hr hA P hP

def geometricPTorsionTrivial (p : ℕ) (hp : p.Prime) (A : ZMod p) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point,
    p • P = 0 → P = 0

/-- The varying printed family has arbitrarily large good primes with
trivial geometric p-torsion for each fixed nonzero integer A. -/
theorem paper5_arbitrarily_large_good_geometric_p_torsion_trivial
    (A : ℤ) (hA : A ≠ 0) (N : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime), N < p ∧ p % 3 = 2 ∧
      (paper5TraceCurve p (A : ZMod p)).Δ ≠ 0 ∧
      geometricPTorsionTrivial p hp (A : ZMod p) := by
  obtain ⟨p, hpB, hp, hp3, hΔ, _⟩ :=
    paper5_arbitrarily_large_good_trace_zero A hA (max N 4)
  have hN : N < p := (le_max_left N 4).trans_lt hpB
  have hp5 : 5 ≤ p := (le_max_right N 4).trans_lt hpB
  have hc : (A : ZMod p) ≠ 0 := by
    intro ha
    apply hΔ
    simp [paper5TraceCurve, ha, ZMod.natCast_self, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, hN, hp3, hΔ, fun P hP =>
    paper5_no_p_torsion_over_algebraicClosure hp5 hp3 hc P hP⟩

end ManuscriptAudit.CubicGeometricTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicGeometricTorsion.paper5_no_geometric_p_torsion,
      ``ManuscriptAudit.CubicGeometricTorsion.paper5_no_p_torsion_over_algebraicClosure,
      ``ManuscriptAudit.CubicGeometricTorsion.paper5_arbitrarily_large_good_geometric_p_torsion_trivial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
