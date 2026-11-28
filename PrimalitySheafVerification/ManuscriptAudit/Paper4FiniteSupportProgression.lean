import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! The literal congruence progression and its finite exceptional support.
The coprimality condition printed on physical pp. 139–140 does not imply disjointness. -/

namespace ManuscriptAudit.Paper4FiniteSupportProgression

open scoped BigOperators

def progression (a q : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p ≡ a [MOD q]}

def avoids (S : Finset ℕ) (a q : ℕ) : Prop :=
  Disjoint (S : Set ℕ) (progression a q)

theorem avoids_iff (S : Finset ℕ) (a q : ℕ) :
    avoids S a q ↔ ∀ p ∈ S, p.Prime → ¬ p ≡ a [MOD q] := by
  constructor
  · intro h p hp hPrime hMod
    exact (Set.disjoint_left.mp h) hp ⟨hPrime, hMod⟩
  · intro h
    apply Set.disjoint_left.mpr
    intro p hp hP
    exact h p hp hP.1 hP.2

/-- The exact support and congruence of the printed criterion can coexist. -/
theorem printed_coprimality_insufficient :
    ¬ ∀ (S : Finset ℕ) a q, (∀ p ∈ S, p.Prime) →
      a.Coprime q → (a * q).Coprime (∏ p ∈ S, p) → avoids S a q := by
  intro h
  let S : Finset ℕ := {3}
  have hPrime : ∀ p ∈ S, p.Prime := by
    intro p hp
    have h3 : p = 3 := Finset.mem_singleton.mp hp
    subst p
    decide
  have hCoprime : (1 * 2 : ℕ).Coprime (∏ p ∈ S, p) := by
    change (1 * 2 : ℕ).Coprime (∏ p ∈ ({3} : Finset ℕ), p)
    rw [Finset.prod_singleton] <;> decide
  have hAvoid := (avoids_iff S 1 2).mp (h S 1 2 hPrime (by decide) hCoprime)
  exact hAvoid 3 (Finset.mem_singleton_self 3) (by decide)
    (show 3 ≡ 1 [MOD 2] by decide)

/-- A modulus larger than every support prime gives an explicit reduced
progression that genuinely avoids that support. -/
theorem avoids_one_of_large_modulus (S : Finset ℕ) (q : ℕ) (hq : 1 < q)
    (hS : ∀ p ∈ S, p < q) : avoids S 1 q := by
  apply (avoids_iff S 1 q).mpr
  intro p hp hPrime hMod
  change p % q = 1 % q at hMod
  rw [Nat.mod_eq_of_lt (hS p hp), Nat.mod_eq_of_lt hq] at hMod
  exact hPrime.ne_one hMod

theorem exists_reduced_avoiding_progression (S : Finset ℕ) :
    ∃ q, 1 < q ∧ (1 : ℕ).Coprime q ∧ avoids S 1 q := by
  let q := S.sup id + 2
  have hq : 1 < q := by
    dsimp [q]
    omega
  refine ⟨q, hq, Nat.coprime_one_left _, avoids_one_of_large_modulus S q hq ?_⟩
  intro p hp
  have hP : p ≤ S.sup id := Finset.le_sup (f := id) hp
  dsimp [q]
  omega

end ManuscriptAudit.Paper4FiniteSupportProgression

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4FiniteSupportProgression.avoids_iff,
      ``ManuscriptAudit.Paper4FiniteSupportProgression.printed_coprimality_insufficient,
      ``ManuscriptAudit.Paper4FiniteSupportProgression.exists_reduced_avoiding_progression] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
