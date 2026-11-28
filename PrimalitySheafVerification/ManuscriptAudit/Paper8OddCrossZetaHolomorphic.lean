import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.LocallyUniformLimit
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossZetaSquareRoot

/-! Normal convergence and holomorphy of the genuine signed cross zeta series above Re(s)=3/4. -/

namespace ManuscriptAudit.Paper8OddCrossZetaHolomorphic

open Set Paper8OddCrossZetaFactorization Paper8OddCrossZetaSquareRoot

noncomputable section

theorem differentiable_oddCrossZetaTerm (j : ℕ) : Differentiable ℂ (fun s => oddCrossZetaTerm s j) := by
  unfold oddCrossZetaTerm crossModulusFactor
  let c : ℝ := 2 * ((j + 1 : ℕ) : ℝ)
  have hc : (((c ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  change Differentiable ℂ (fun s => _ * ((↑((c ^ 2)⁻¹ : ℝ) : ℂ) ^ s))
  simp_rw [Complex.cpow_def_of_ne_zero hc]
  exact differentiable_const.mul (Complex.differentiable_exp.comp (differentiable_const.mul differentiable_id))

theorem norm_oddCrossZetaTerm_antitone_re {s t : ℂ} (h : s.re ≤ t.re) (j : ℕ) :
    ‖oddCrossZetaTerm t j‖ ≤ ‖oddCrossZetaTerm s j‖ := by
  let c : ℝ := 2 * ((j + 1 : ℕ) : ℝ)
  have hc : 1 ≤ c := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    unfold c
    push_cast
    linarith
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  unfold oddCrossZetaTerm
  rw [norm_mul, norm_mul, crossModulusFactor_norm t hcp, crossModulusFactor_norm s hcp]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc (by linarith)) (norm_nonneg _)

theorem oddCrossZeta_analyticOnNhd :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' j : ℕ, oddCrossZetaTerm s j) {s : ℂ | (3 / 4 : ℝ) < s.re} := by
  have hOpen : IsOpen {s : ℂ | (3 / 4 : ℝ) < s.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hOpen
  intro s hs
  obtain ⟨t, ht, hts⟩ := exists_between (show (3 / 4 : ℝ) < s.re from hs)
  let U : Set ℂ := {z : ℂ | t < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hT : (3 / 4 : ℝ) < (t : ℂ).re := by simpa only [Complex.ofReal_re] using ht
  have hSum := oddCrossZetaTerm_abs_summable_threeQuarter (t : ℂ) hT
  have hBound (j : ℕ) (z : ℂ) (hz : z ∈ U) : ‖oddCrossZetaTerm z j‖ ≤ ‖oddCrossZetaTerm (t : ℂ) j‖ := by
    apply norm_oddCrossZetaTerm_antitone_re
    rw [Complex.ofReal_re]
    exact (show t < z.re from hz).le
  have hD : DifferentiableOn ℂ (fun z : ℂ => ∑' j : ℕ, oddCrossZetaTerm z j) U :=
    Complex.differentiableOn_tsum_of_summable_norm hSum
      (fun j => (differentiable_oddCrossZetaTerm j).differentiableOn) hU hBound
  exact ((hD s hts).differentiableAt (hU.mem_nhds hts)).differentiableWithinAt

end
end ManuscriptAudit.Paper8OddCrossZetaHolomorphic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossZetaHolomorphic.oddCrossZeta_analyticOnNhd
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
