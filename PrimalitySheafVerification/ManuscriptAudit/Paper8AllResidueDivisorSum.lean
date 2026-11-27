import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Divisors
import PrimalitySheafVerification.ManuscriptAudit.Paper8GcdArithmeticWeight

/-! Finite divisor decomposition of the all-residue Dedekind-exponential row. -/

namespace ManuscriptAudit.Paper8AllResidueDivisorSum

open Paper8GcdArithmeticWeight

noncomputable section

def reducedFrequencySum (m : ℕ) (u : ℝ) : ℂ :=
  ∑ d ∈ (Finset.univ.filter (fun d : Fin m => Nat.Coprime d.val m)), frequencyWeight m u d

theorem all_frequency_sum_eq_divisor_sum {m : ℕ} (hm : 0 < m) (u : ℝ) :
    (∑ d : Fin m, frequencyWeight m u d) =
      ∑ g ∈ m.divisors, reducedFrequencySum (m/g) u := by
  have hmapping : ∀ d ∈ (Finset.univ : Finset (Fin m)), Nat.gcd d.val m ∈ m.divisors := by
    intro d _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hm.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmapping (frequencyWeight m u)]
  apply Finset.sum_congr rfl
  intro g hgMem
  have hd := Nat.dvd_of_mem_divisors hgMem
  obtain ⟨n, rfl⟩ := hd
  have hg : 0 < g := Nat.pos_of_ne_zero fun h => by simp [h] at hm
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hm
  have hc : (g*n)/g = n := Nat.mul_div_cancel_left n hg
  rw [hc, reducedFrequencySum]
  exact gcd_class_eq_reduced_frequency_sum hg hn u

end
end ManuscriptAudit.Paper8AllResidueDivisorSum

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8AllResidueDivisorSum.all_frequency_sum_eq_divisor_sum
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
