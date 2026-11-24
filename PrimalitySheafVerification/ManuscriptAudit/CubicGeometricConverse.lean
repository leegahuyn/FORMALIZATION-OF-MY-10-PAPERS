import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import PrimalitySheafVerification.ManuscriptAudit.CubicTrace

/-!
# Divisibility of the finite point count and geometric torsion

For the Paper 5 cubic, a prime divisor of the actual point count over
a finite coefficient field gives a nonidentity point killed by that prime
over the algebraic closure. The finite count remains an input to this
implication.
-/

namespace ManuscriptAudit.CubicGeometricConverse

open WeierstrassCurve
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

/-- Cauchy's theorem for the projective points, followed by an injective
point map into the algebraic closure of the base field. -/
theorem exists_algebraicClosure_point_of_card_dvd
    {F L : Type*} [Field F] [Field L] [Finite L] [Algebra F L]
    (W : WeierstrassCurve F) (p : ℕ) [Fact p.Prime]
    (hCard : p ∣ Nat.card (W.baseChange L).toProjective.Point) :
    ∃ P : (W.baseChange (AlgebraicClosure F)).toProjective.Point, P ≠ 0 ∧ p • P = 0 := by
  classical
  let eL := Projective.Point.toAffineAddEquiv (W := (W.baseChange L).toProjective)
  let eFinite := eL.toEquiv.trans ((W.baseChange L).toAffine.nonsingularPointEquiv)
  letI : Finite (W.baseChange L).toProjective.Point :=
    Finite.of_injective eFinite eFinite.injective
  obtain ⟨P, hOrder⟩ := exists_prime_addOrderOf_dvd_card' p hCard
  have hP : p • P = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    simpa only [hOrder] using (dvd_rfl : p ∣ p)
  have hPne : P ≠ 0 := by
    intro hz
    exact (Fact.out : p.Prime).ne_one
      (hOrder.symm.trans (AddMonoid.addOrderOf_eq_one_iff.mpr hz))
  letI : Module.Finite F L := Module.Finite.of_finite
  letI : Algebra.IsAlgebraic F L := ⟨fun z => (IsIntegral.of_finite F z).isAlgebraic⟩
  let i : L →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let eC := Projective.Point.toAffineAddEquiv
    (W := (W.baseChange (AlgebraicClosure F)).toProjective)
  let g : (W.baseChange L).toAffine.Point →+
      (W.baseChange (AlgebraicClosure F)).toAffine.Point :=
    Affine.Point.map (W' := W.toAffine) i
  have hg : Function.Injective g := Affine.Point.map_injective (W' := W.toAffine) i
  let f : (W.baseChange L).toProjective.Point →+
      (W.baseChange (AlgebraicClosure F)).toProjective.Point :=
    eC.symm.toAddMonoidHom.comp (g.comp eL.toAddMonoidHom)
  have hf : Function.Injective f := eC.symm.injective.comp (hg.comp eL.injective)
  refine ⟨f P, ?_, ?_⟩
  · intro h
    exact hPne (hf (h.trans f.map_zero.symm))
  · rw [← map_nsmul, hP, map_zero]

/-- The group-order divisibility implication for the actual printed cubic
over an arbitrary finite field extension of the residue field. -/
theorem paper5_geometric_p_torsion_of_finite_projective_card_dvd
    {p : ℕ} [Fact p.Prime] {A : ZMod p}
    {L : Type*} [Field L] [Finite L] [Algebra (ZMod p) L]
    (hCard : p ∣ Nat.card ((paper5TraceCurve p A).baseChange L).toProjective.Point) :
    ∃ P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point,
      P ≠ 0 ∧ p • P = 0 :=
  exists_algebraicClosure_point_of_card_dvd (paper5TraceCurve p A) p hCard

/-- The same implication when the finite field is Mathlib's GaloisField. -/
theorem paper5_geometric_p_torsion_of_galoisField_projective_card_dvd
    {p : ℕ} [Fact p.Prime] (r : ℕ) {A : ZMod p}
    (hCard : p ∣ Nat.card
      ((paper5TraceCurve p A).baseChange (GaloisField p r)).toProjective.Point) :
    ∃ P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point,
      P ≠ 0 ∧ p • P = 0 :=
  paper5_geometric_p_torsion_of_finite_projective_card_dvd hCard

end ManuscriptAudit.CubicGeometricConverse

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicGeometricConverse.exists_algebraicClosure_point_of_card_dvd,
      ``ManuscriptAudit.CubicGeometricConverse.paper5_geometric_p_torsion_of_finite_projective_card_dvd,
      ``ManuscriptAudit.CubicGeometricConverse.paper5_geometric_p_torsion_of_galoisField_projective_card_dvd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
