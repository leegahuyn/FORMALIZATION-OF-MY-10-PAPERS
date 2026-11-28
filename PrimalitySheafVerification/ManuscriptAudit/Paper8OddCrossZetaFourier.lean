import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossFourierExpansion
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossZetaRemainder

/-! Exact arithmetic zeta identity for the complete first cross-cusp Fourier coefficient. -/

namespace ManuscriptAudit.Paper8OddCrossZetaFourier

open Filter MeasureTheory
open Paper8OddCrossCuspCutoff Paper8OddCrossPoincareConvergence Paper8OddCrossPoincareTranslate
open Paper8OddCrossPoincareRowKernel Paper8OddCrossPoincareUnfold Paper8OddCrossFourierExpansion
open Paper8OddCrossZetaFactorization Paper8OddCrossZetaRemainder

noncomputable section

def oddCrossZeta (s : ℂ) : ℂ := ∑' D : ℕ, oddCrossZetaTerm s D

def oddCrossZetaRemainder (s : ℂ) (y : ℝ) : ℂ := ∑' D : ℕ, oddCrossRemainderTerm s y D

theorem odd_cross_fourier_eq_zeta (s : ℂ) (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..(1 : ℝ), ∑' i : CrossIndex, oddCrossFourierTerm s (pointAtHeight x hy) i) =
      oddCrossZeta s * (∫ u : ℝ, crossLeadingKernel s y u) + oddCrossZetaRemainder s y := by
  let L := ∫ u : ℝ, crossLeadingKernel s y u
  have hs' : (1 / 2 : ℝ) < s.re := by linarith
  have hL := crossLeadingKernel_integrable s hs' hy
  have hTerm (D : ℕ) :
      crossSum (Nat.succ_pos D) * (∫ u : ℝ, crossRealKernel s y (2 * ((D + 1 : ℕ) : ℝ)) u) =
        oddCrossZetaTerm s D * L + oddCrossRemainderTerm s y D := by
    let c : ℝ := 2 * ((D + 1 : ℕ) : ℝ)
    have hc : 1 ≤ c := by
      have hD : 0 ≤ (D : ℝ) := by positivity
      unfold c
      push_cast
      linarith
    have hc' : 0 < c := lt_of_lt_of_le zero_lt_one hc
    have hI : (∫ u : ℝ, crossRealKernel s y c u) =
        ∫ u : ℝ, crossModulusFactor s c * (crossLeadingKernel s y u + crossRemainderKernel s y c u) :=
      integral_congr_ae (Eventually.of_forall (crossRealKernel_factor s hy hc'))
    change crossSum (Nat.succ_pos D) * (∫ u : ℝ, crossRealKernel s y c u) = _
    rw [hI, integral_const_mul, integral_add hL (crossRemainderKernel_integrable s hs' hy hc)]
    unfold oddCrossRemainderTerm oddCrossZetaTerm L
    fold c
    ring
  rw [odd_cross_fourier_expansion s hs hy, tsum_congr hTerm]
  have hZ : Summable (fun D : ℕ => oddCrossZetaTerm s D) :=
    (oddCrossZetaTerm_abs_summable s hs).of_norm
  have hR : Summable (fun D : ℕ => oddCrossRemainderTerm s y D) :=
    (oddCrossRemainderTerm_abs_summable s hs' hy).of_norm
  rw [Summable.tsum_add (hZ.mul_right L) hR, tsum_mul_right]
  rfl

end
end ManuscriptAudit.Paper8OddCrossZetaFourier

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossZetaFourier.odd_cross_fourier_eq_zeta
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
