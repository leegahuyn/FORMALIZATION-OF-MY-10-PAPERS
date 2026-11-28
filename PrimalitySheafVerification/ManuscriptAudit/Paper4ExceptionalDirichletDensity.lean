import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper4ExceptionalPrimeProgression
import PrimalitySheafVerification.ManuscriptAudit.Paper4PrimeDirichletExceptions

/-! Paper 4, physical pp. 139–140: genuine Dirichlet limits for the
literal primes dividing the gcd or discriminant, and their complement. -/

namespace ManuscriptAudit.Paper4ExceptionalDirichletDensity

open Filter Topology
open Paper4ExceptionalPrimeProgression (exceptional prime_mem_exceptional_iff)
open FiniteSupportDirichletLimit (normalizer finiteWeight normalized_finiteWeight_tendsto_zero)

noncomputable section

/-- The series over actual primes dividing at least one of the two integers. -/
def exceptionalWeight (g d : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime ∧ (n ∣ g ∨ n ∣ d) then (n : ℝ) ^ (-s) else 0

private theorem prime_of_mem_exceptional {g d p : ℕ} (hp : p ∈ exceptional g d) : p.Prime :=
  (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors

theorem exceptionalWeight_eq_finiteWeight {g d : ℕ} (hg : g ≠ 0) (hd : d ≠ 0) (s : ℝ) :
    exceptionalWeight g d s = finiteWeight (exceptional g d) s := by
  unfold exceptionalWeight finiteWeight
  rw [tsum_eq_sum (s := exceptional g d) ?_]
  · apply Finset.sum_congr rfl
    intro n hn
    have hPrime := prime_of_mem_exceptional hn
    simp [hPrime, (prime_mem_exceptional_iff hg hd hPrime).mp hn]
  · intro n hn
    by_cases hPrime : n.Prime
    · have hDiv : ¬ (n ∣ g ∨ n ∣ d) :=
        fun h ↦ hn ((prime_mem_exceptional_iff hg hd hPrime).mpr h)
      simp [hDiv]
    · simp [hPrime]

/-- The literal exceptional prime series has Dirichlet density zero. -/
theorem exceptional_dirichlet_density {g d : ℕ} (hg : g ≠ 0) (hd : d ≠ 0) :
    Tendsto (fun s ↦ exceptionalWeight g d s / normalizer s) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  simpa only [exceptionalWeight_eq_finiteWeight hg hd] using
    normalized_finiteWeight_tendsto_zero (exceptional g d)
      (fun _ hn ↦ (prime_of_mem_exceptional hn).pos)

/-- A reduced progression retains its actual Dirichlet density among those primes
that divide neither the fixed gcd nor the fixed discriminant. -/
theorem good_progression_dirichlet_density {a q g d : ℕ} [NeZero q]
    (ha : a.Coprime q) (hg : g ≠ 0) (hd : d ≠ 0) :
    Tendsto (fun s : ℝ ↦ (∑' n : ℕ, if n.Prime ∧ (n ≡ a [MOD q]) ∧
      ¬ n ∣ g ∧ ¬ n ∣ d then (n : ℝ) ^ (-s) else 0) / normalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply (Paper4PrimeDirichletExceptions.reduced_progression_density (exceptional g d) a ha).congr
  intro s
  congr 1
  apply tsum_congr
  intro n
  by_cases hPrime : n.Prime
  · have hNot : n ∉ exceptional g d ↔ ¬ n ∣ g ∧ ¬ n ∣ d :=
      (not_congr (prime_mem_exceptional_iff hg hd hPrime)).trans not_or
    simp only [hPrime, true_and, hNot]
  · simp [hPrime]

end
end ManuscriptAudit.Paper4ExceptionalDirichletDensity

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4ExceptionalDirichletDensity.exceptionalWeight_eq_finiteWeight,
      ``ManuscriptAudit.Paper4ExceptionalDirichletDensity.exceptional_dirichlet_density,
      ``ManuscriptAudit.Paper4ExceptionalDirichletDensity.good_progression_dirichlet_density] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
