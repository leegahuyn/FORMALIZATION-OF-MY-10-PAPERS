import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportAbsoluteHigher
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportScalar
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHTwo
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectivePrimeHOne

/-! The native split affine node has compact Betti dimensions 0, 1, 1, 0, … for invertible prime coefficients. -/

namespace ManuscriptAudit.NodalFiniteCohomology

open AlgebraicGeometry CategoryTheory
open NodalCompactSupportHOne (nodalHc)
open NodalCompactSupportScalar (coefficient compactModule)
open scoped BigOperators

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt compactModule

variable (K : Type) [Field K] [IsAlgClosed K]
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The compactly supported Betti number of the actual affine nodal scheme. -/
def betti (n : ℕ) : ℕ :=
  Module.finrank (ZMod ℓ) (nodalHc K (coefficient ℓ) n)

private def linearOfAddEquiv {E : Type} [AddCommGroup E] [Module (ZMod ℓ) E]
    (e : E ≃+ ZMod ℓ) : E ≃ₗ[ZMod ℓ] ZMod ℓ :=
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap ℓ) e.bijective

theorem betti_zero : betti K ℓ 0 = 0 := by
  letI := NodalCompactSupportHZero.compact_HZero_subsingleton K (coefficient ℓ)
  exact Module.finrank_zero_of_subsingleton

variable [NeZero (ℓ : K)]

theorem betti_one (h2 : (2 : K) ≠ 0) : betti K ℓ 1 = 1 :=
  (LinearEquiv.finrank_eq
    (linearOfAddEquiv ℓ (NodalProjectivePrimeHOne.compactHOneEquiv K h2 ℓ))).trans
    (Module.finrank_self _)

theorem betti_two (h2 : (2 : K) ≠ 0) : betti K ℓ 2 = 1 :=
  (LinearEquiv.finrank_eq
    (linearOfAddEquiv ℓ (NodalProjectiveHTwo.compactHTwoEquiv K ℓ h2))).trans
    (Module.finrank_self _)

theorem betti_add_three (h2 : (2 : K) ≠ 0) (n : ℕ) : betti K ℓ (n + 3) = 0 := by
  letI := NodalCompactSupportAbsoluteHigher.compact_H_add_three_subsingleton K h2 ℓ n
  exact Module.finrank_zero_of_subsingleton

/-- These dimensions are those of actual finite-dimensional groups in every degree. -/
theorem compact_finiteDimensional (h2 : (2 : K) ≠ 0) (n : ℕ) :
    FiniteDimensional (ZMod ℓ) (nodalHc K (coefficient ℓ) n) := by
  letI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  cases n with
  | zero =>
    letI := NodalCompactSupportHZero.compact_HZero_subsingleton K (coefficient ℓ)
    letI : Finite (nodalHc K (coefficient ℓ) 0) := inferInstance
    infer_instance
  | succ n =>
    cases n with
    | zero =>
      let e := linearOfAddEquiv ℓ (NodalProjectivePrimeHOne.compactHOneEquiv K h2 ℓ)
      exact FiniteDimensional.of_injective e.toLinearMap e.injective
    | succ n =>
      cases n with
      | zero =>
        let e := linearOfAddEquiv ℓ (NodalProjectiveHTwo.compactHTwoEquiv K ℓ h2)
        exact FiniteDimensional.of_injective e.toLinearMap e.injective
      | succ n =>
        letI := NodalCompactSupportAbsoluteHigher.compact_H_add_three_subsingleton K h2 ℓ n
        letI : Finite (nodalHc K (coefficient ℓ) (n + 3)) := inferInstance
        infer_instance

/-- Every truncation containing degrees zero, one and two gives the true compact Euler characteristic zero. -/
theorem complete_compact_euler (h2 : (2 : K) ≠ 0) (N : ℕ) (hN : 3 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (betti K ℓ n : ℤ)) = 0 := by
  calc
    _ = ∑ n ∈ Finset.range 3, (-1 : ℤ) ^ n * (betti K ℓ n : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro i _ hMiss
      have hi : 3 ≤ i := Nat.le_of_not_gt (fun hh ↦ hMiss (Finset.mem_range.mpr hh))
      have h : i = (i - 3) + 3 := (Nat.sub_add_cancel hi).symm
      have hZero : betti K ℓ i = 0 := by rw [h, betti_add_three K ℓ h2]
      simp [hZero]
    _ = 0 := by
      norm_num [Finset.sum_range_succ, betti_zero K ℓ, betti_one K ℓ h2, betti_two K ℓ h2]

end
end ManuscriptAudit.NodalFiniteCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalFiniteCohomology.betti_zero,
      ``ManuscriptAudit.NodalFiniteCohomology.betti_one,
      ``ManuscriptAudit.NodalFiniteCohomology.betti_two,
      ``ManuscriptAudit.NodalFiniteCohomology.betti_add_three,
      ``ManuscriptAudit.NodalFiniteCohomology.compact_finiteDimensional,
      ``ManuscriptAudit.NodalFiniteCohomology.complete_compact_euler] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
