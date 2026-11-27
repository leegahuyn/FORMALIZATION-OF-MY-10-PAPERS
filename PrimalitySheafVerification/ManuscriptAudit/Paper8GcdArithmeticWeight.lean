import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8GcdResidueFiber
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindCommonDivisor

/-! The actual Dedekind-exponential frequency weight on one residue gcd class. -/

namespace ManuscriptAudit.Paper8GcdArithmeticWeight

open Paper8ContourResidueWeights
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8GcdResidueFiber Paper8DedekindCommonDivisor

noncomputable section

def frequencyWeight (m : ℕ) (u : ℝ) (d : Fin m) : ℂ :=
  Complex.exp (periodCoefficient *
    ((dedekindSum (-(d.val : ℤ)) m : ℝ)/2 + u*(d.val : ℝ)/(m : ℝ) : ℝ))

theorem weight_of_multiple {g n : ℕ} (hg : 0 < g) (hn : 0 < n) (u : ℝ) (i : Fin n) :
    frequencyWeight (g*n) u (multiplyResidue hg i) = frequencyWeight n u i := by
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hD : dedekindSum (-(↑(g*i.val) : ℤ)) (g*n) = dedekindSum (-(i.val : ℤ)) n := by
    rw [Nat.cast_mul, ← mul_neg]
    exact scaled_dedekind_sum _ hg hn
  have hF : u * (↑(g*i.val) : ℝ) / (↑(g*n) : ℝ) = u * (i.val : ℝ) / (n : ℝ) := by
    push_cast
    field_simp [hgR.ne', hnR.ne'] <;> ring
  unfold frequencyWeight
  change Complex.exp (periodCoefficient *
      ((dedekindSum (-(↑(g*i.val) : ℤ)) (g*n) : ℝ)/2 +
        u*(↑(g*i.val) : ℝ)/(↑(g*n) : ℝ) : ℝ)) = _
  rw [hD, hF]

theorem gcd_class_eq_reduced_frequency_sum {g n : ℕ} (hg : 0 < g) (hn : 0 < n) (u : ℝ) :
    (∑ d ∈ (Finset.univ.filter (fun d : Fin (g*n) => Nat.gcd d.val (g*n) = g)),
      frequencyWeight (g*n) u d) =
    ∑ i ∈ (Finset.univ.filter (fun i : Fin n => Nat.Coprime i.val n)), frequencyWeight n u i := by
  rw [sum_gcd_fiber hg]
  exact Finset.sum_congr rfl (fun i _ => weight_of_multiple hg hn u i)

end
end ManuscriptAudit.Paper8GcdArithmeticWeight

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8GcdArithmeticWeight.weight_of_multiple,
      ``ManuscriptAudit.Paper8GcdArithmeticWeight.gcd_class_eq_reduced_frequency_sum] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
