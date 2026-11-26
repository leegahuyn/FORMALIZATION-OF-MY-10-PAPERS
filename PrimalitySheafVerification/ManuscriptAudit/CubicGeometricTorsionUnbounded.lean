import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LSeries.PrimesInAP
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsionLowerBound

/-!
# Unbounded geometric p-torsion in the varying printed cubic family

For the varying family with A = 1 and p_n = p, every prime p = 1
modulo 3 above 5 gives an actual geometric p-torsion group containing
p distinct points. Dirichlet's theorem makes those lower bounds
unbounded. Consequently this varying family cannot have a finite
partition carrying uniformly finite stalk labels on each piece.
-/

namespace ManuscriptAudit.CubicGeometricTorsionUnbounded

open CubicGeometricTorsionLowerBound

noncomputable section

/-- No finite set of labels can hold the actual geometric torsion
for every ordinary prime of this varying family. -/
theorem arbitrarily_large_geometric_torsion (N : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime), N < p ∧ 5 ≤ p ∧ p % 3 = 1 ∧
      letI : Fact p.Prime := ⟨hp⟩
      ¬ Nonempty (geometricPTorsion p (1 : ZMod p) ↪ Fin N) := by
  obtain ⟨p, hpBound, hp, hpMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N 5) (q := 3) (a := 1) (by decide) (by decide)
  have hN : N < p := lt_of_le_of_lt (le_max_left N 5) hpBound
  have h5 : 5 ≤ p := le_of_lt (lt_of_le_of_lt (le_max_right N 5) hpBound)
  have hMod : p % 3 = 1 := by simpa [Nat.ModEq] using hpMod
  refine ⟨p, hp, hN, h5, hMod, ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  obtain ⟨e⟩ := paper5_geometric_p_torsion_contains_fin h5 hMod
    (one_ne_zero : (1 : ZMod p) ≠ 0)
  obtain ⟨f⟩ := h
  have hSize := Fintype.card_le_of_injective (fun x : Fin p => f (e x))
    (f.injective.comp e.injective)
  have hpSize : p ≤ N := by simpa using hSize
  exact (not_le_of_gt hN) hpSize

/-- A finite family of stalk cardinality bounds cannot describe the varying family. -/
theorem no_finite_stratum_bounds {I : Type*} [Fintype I] (bound : I → ℕ) :
    ¬ ∀ (p : ℕ) (hp : p.Prime), 5 ≤ p → p % 3 = 1 →
      letI : Fact p.Prime := ⟨hp⟩
      ∃ i : I, Nonempty (geometricPTorsion p (1 : ZMod p) ↪ Fin (bound i)) := by
  classical
  let N := Finset.univ.sup bound
  obtain ⟨p, hp, _, h5, hm, h⟩ := arbitrarily_large_geometric_torsion N
  letI : Fact p.Prime := ⟨hp⟩
  intro hBounds
  obtain ⟨i, ⟨e⟩⟩ := hBounds p hp h5 hm
  have hi : bound i ≤ N := Finset.le_sup (Finset.mem_univ i)
  let f : Fin (bound i) ↪ Fin N :=
    ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hi⟩,
      by
        intro j k hj
        exact Fin.ext (congrArg (fun v : Fin N => v.val) hj)⟩
  exact h ⟨⟨fun x => f (e x), f.injective.comp e.injective⟩⟩

end

end ManuscriptAudit.CubicGeometricTorsionUnbounded

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicGeometricTorsionUnbounded.arbitrarily_large_geometric_torsion,
      ``ManuscriptAudit.CubicGeometricTorsionUnbounded.no_finite_stratum_bounds] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
