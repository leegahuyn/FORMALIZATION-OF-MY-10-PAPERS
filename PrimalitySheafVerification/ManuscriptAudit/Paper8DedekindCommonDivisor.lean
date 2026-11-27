import Lean.Util.CollectAxioms
import Mathlib.Logic.Equiv.Fin.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8SawtoothDistribution

/-! A common divisor of a residue and its modulus reduces the literal Dedekind sum exactly. -/

namespace ManuscriptAudit.Paper8DedekindCommonDivisor

open Paper8ContourResidueWeights Paper8SawtoothDistribution

theorem scaled_dedekind_sum (a : ℤ) {g n : ℕ} (hg : 0 < g) (hn : 0 < n) :
    dedekindSum ((g : ℤ)*a) (g*n) = dedekindSum a n := by
  have hgq : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  let e : Fin n × Fin g ≃ Fin (g*n) :=
    (Equiv.prodComm (Fin n) (Fin g)).trans finProdFinEquiv
  let F (i : Fin (g*n)) : ℚ :=
    sawtooth ((i.val : ℚ)/((g*n : ℕ) : ℚ)) *
      sawtooth ((((g : ℤ)*a : ℤ) : ℚ)*(i.val : ℚ)/((g*n : ℕ) : ℚ))
  have hValues (i : Fin n) (j : Fin g) :
      F (e (i,j)) = sawtooth (((i.val : ℚ)/(n : ℚ)+(j.val : ℚ))/(g : ℚ)) *
        sawtooth ((a : ℚ)*(i.val : ℚ)/(n : ℚ)) := by
    change sawtooth (((i.val+n*j.val : ℕ) : ℚ)/((g*n : ℕ) : ℚ)) *
      sawtooth ((((g : ℤ)*a : ℤ) : ℚ)*((i.val+n*j.val : ℕ) : ℚ)/((g*n : ℕ) : ℚ)) = _
    have h₁ : (((i.val+n*j.val : ℕ) : ℚ)/((g*n : ℕ) : ℚ)) =
        ((i.val : ℚ)/(n : ℚ)+(j.val : ℚ))/(g : ℚ) := by
      push_cast
      field_simp [hnq.ne', hgq.ne'] <;> ring
    have h₂ : (((g : ℤ)*a : ℤ) : ℚ)*((i.val+n*j.val : ℕ) : ℚ)/((g*n : ℕ) : ℚ) =
        (a : ℚ)*(i.val : ℚ)/(n : ℚ)+((a*(j.val : ℤ) : ℤ) : ℚ) := by
      push_cast
      field_simp [hnq.ne', hgq.ne'] <;> ring
    rw [h₁, h₂, sawtooth_int_translate]
  calc
    dedekindSum ((g : ℤ)*a) (g*n) = ∑ k : Fin (g*n), F k := rfl
    _ = ∑ ij : Fin n × Fin g, F (e ij) := (Equiv.sum_comp e F).symm
    _ = ∑ i : Fin n, ∑ j : Fin g, F (e (i,j)) := by rw [Fintype.sum_prod_type]
    _ = dedekindSum a n := by
      unfold dedekindSum
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [hValues, ← Finset.sum_mul]
      have h0 : (0 : ℚ) ≤ (i.val : ℚ)/(n : ℚ) := div_nonneg (Nat.cast_nonneg _) hnq.le
      have h1 : (i.val : ℚ)/(n : ℚ) < 1 :=
        (div_lt_one₀ hnq).2 (by exact_mod_cast i.isLt)
      rw [distribution g hg h0 h1]

end ManuscriptAudit.Paper8DedekindCommonDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8DedekindCommonDivisor.scaled_dedekind_sum
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
