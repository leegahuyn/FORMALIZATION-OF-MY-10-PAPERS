import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricConverse
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicTraceClassification

/-!
# Geometric p-torsion in the printed varying cubic family

The count from the nonzero Hasse coefficient in the residue class one
modulo three gives geometric p-torsion by Cauchy's theorem over a finite
extension. The existing residue-class-two calculation gives the converse.
-/

namespace ManuscriptAudit.CubicGeometricClassification

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open CubicTraceClassification

/-- Actual geometric p-torsion of the printed varying family is trivial
exactly in the residue class two modulo three. -/
theorem paper5_trivial_geometric_p_torsion_iff {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    (∀ P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point,
      p • P = 0 → P = 0) ↔ p % 3 = 2 := by
  classical
  refine ⟨?_, fun hr => CubicGeometricTorsion.paper5_no_p_torsion_over_algebraicClosure hp5 hr hA⟩
  intro h
  by_contra hn
  have h0 := prime_rem_three_ne_zero (p := p) hp5
  have hr : p % 3 = 1 := by omega
  let r := p - 1
  let F := GaloisField p r
  letI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ (p - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p r (by dsimp [r]; omega)
  obtain ⟨P, hP, hz⟩ :=
    CubicGeometricConverse.paper5_geometric_p_torsion_of_galoisField_projective_card_dvd r
      (paper5_extension_count_dvd hc hp5 hr hA)
  exact hP (h P hz)

/-- Trace zero and trivial geometric p-torsion agree for every stated
good reduction of the printed varying family. -/
theorem paper5_trace_zero_iff_trivial_geometric_p_torsion {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    ((p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ) = 0) ↔
      (∀ P : ((paper5TraceCurve p A).baseChange (AlgebraicClosure (ZMod p))).toProjective.Point,
        p • P = 0 → P = 0) :=
  (paper5_trace_eq_zero_iff hp5 hA).trans (paper5_trivial_geometric_p_torsion_iff hp5 hA).symm


end ManuscriptAudit.CubicGeometricClassification

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CubicGeometricClassification.paper5_trivial_geometric_p_torsion_iff,
      ``ManuscriptAudit.CubicGeometricClassification.paper5_trace_zero_iff_trivial_geometric_p_torsion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
