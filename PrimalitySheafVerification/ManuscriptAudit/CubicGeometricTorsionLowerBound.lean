import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.OrderOfElement
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricClassification

/-!
# A cyclic subgroup in the actual geometric p-torsion

In the residue class one modulo three, every nonzero parameter in the
printed varying family gives a geometric point of order p. Its multiples
give p distinct actual geometric p-torsion points.
-/

namespace ManuscriptAudit.CubicGeometricTorsionLowerBound

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

abbrev geometricPoints (p : ℕ) [Fact p.Prime] (A : ZMod p) :=
  ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point

abbrev geometricPTorsion (p : ℕ) [Fact p.Prime] (A : ZMod p) :=
  {P : geometricPoints p A // p • P = 0}

theorem exists_geometricPoint_of_order_prime {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) :
    ∃ P : geometricPoints p A, addOrderOf P = p := by
  classical
  by_contra hNone
  have hTrivial : ∀ P : geometricPoints p A, p • P = 0 → P = 0 := by
    intro P hpP
    by_contra hP
    exact hNone ⟨P, addOrderOf_eq_prime hpP hP⟩
  have hTwo :=
    (CubicGeometricClassification.paper5_trivial_geometric_p_torsion_iff hp5 hA).mp hTrivial
  rw [hr] at hTwo
  exact (by decide : (1 : ℕ) ≠ 2) hTwo

theorem paper5_geometric_p_torsion_contains_fin {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) :
    Nonempty (Fin p ↪ geometricPTorsion p A) := by
  obtain ⟨P, hOrder⟩ := exists_geometricPoint_of_order_prime hp5 hr hA
  have hz : p • P = 0 := by
    simpa only [hOrder] using addOrderOf_nsmul_eq_zero P
  refine ⟨⟨fun i => ⟨i.val • P, ?_⟩, ?_⟩⟩
  · rw [← mul_nsmul, Nat.mul_comm p i.val, mul_nsmul, hz, nsmul_zero]
  · intro i j hij
    apply Fin.ext
    have hi : i.val ∈ Set.Iio (addOrderOf P) := by
      rw [hOrder]
      exact i.isLt
    have hj : j.val ∈ Set.Iio (addOrderOf P) := by
      rw [hOrder]
      exact j.isLt
    exact nsmul_injOn_Iio_addOrderOf hi hj (congrArg Subtype.val hij)

end ManuscriptAudit.CubicGeometricTorsionLowerBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.CubicGeometricTorsionLowerBound.exists_geometricPoint_of_order_prime,
        ``ManuscriptAudit.CubicGeometricTorsionLowerBound.paper5_geometric_p_torsion_contains_fin] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
