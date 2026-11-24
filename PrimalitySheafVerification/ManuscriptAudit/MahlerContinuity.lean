import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# A continuous p-adic Mahler cutoff

Paper 8, physical PDF p. 380, §4.2 concerns truncation at fixed
p-adic precision. Continuity of the actual function on the p-adic
integers gives coefficient decay and uniform accuracy of the actual
Mahler partial sums. The cutoff may depend on the function and precision.
-/

open Filter
open scoped BigOperators fwdDiff Topology

namespace ManuscriptAudit.MahlerContinuity

variable {p : ℕ} [hp : Fact p.Prime]

/-- At each precision, a genuine continuous p-adic function has a cutoff
beyond any fixed prefix. All subsequent Mahler coefficients are divisible
by the precision modulus and all subsequent partial sums approximate the
function at that modulus on the whole p-adic domain. -/
theorem exists_mahler_cutoff (f : C(ℤ_[p], ℤ_[p])) (k minCutoff : ℕ) :
    ∃ N : ℕ, minCutoff ≤ N ∧
      (∀ j ≥ N, (p : ℤ_[p]) ^ k ∣ Δ_[1]^[j] f 0) ∧
      ∀ m ≥ N, ∀ x : ℤ_[p], (p : ℤ_[p]) ^ k ∣
        (show C(ℤ_[p], ℤ_[p]) from
          f - ∑ j ∈ Finset.range m, PadicInt.mahlerTerm (Δ_[1]^[j] f 0) j) x := by
  let threshold : ℝ := (p : ℝ) ^ (-(k : ℤ))
  have hThreshold : 0 < threshold := zpow_pos (Nat.cast_pos.mpr hp.out.pos) _
  let truncation (m : ℕ) : C(ℤ_[p], ℤ_[p]) :=
    ∑ j ∈ Finset.range m, PadicInt.mahlerTerm (Δ_[1]^[j] f 0) j
  have hPartial : Tendsto truncation atTop (𝓝 f) :=
    (PadicInt.hasSum_mahler f).tendsto_sum_nat
  have hApprox : Tendsto (fun m : ℕ => f - truncation m) atTop (𝓝 (0 : C(ℤ_[p], ℤ_[p]))) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f)).sub hPartial
  have hCoeff := (NormedAddGroup.tendsto_nhds_zero.mp (PadicInt.fwdDiff_tendsto_zero f))
    threshold hThreshold
  have hError := (NormedAddGroup.tendsto_nhds_zero.mp hApprox) threshold hThreshold
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hCoeff.and hError)
  have hDvd (x : ℤ_[p]) (hx : ‖x‖ ≤ threshold) : (p : ℤ_[p]) ^ k ∣ x :=
    Ideal.mem_span_singleton.mp ((PadicInt.norm_le_pow_iff_mem_span_pow x k).mpr hx)
  refine ⟨max minCutoff N, le_max_left _ _, ?_, ?_⟩
  · intro j hj
    exact hDvd _ (hN j ((le_max_right _ _).trans hj)).1.le
  · intro m hm x
    let error : C(ℤ_[p], ℤ_[p]) := f - truncation m
    change (p : ℤ_[p]) ^ k ∣ error x
    have hEval : ‖error x‖ ≤ ‖error‖ := error.norm_coe_le_norm x
    exact hDvd _ (hEval.trans (hN m ((le_max_right _ _).trans hm)).2.le)

end ManuscriptAudit.MahlerContinuity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.MahlerContinuity.exists_mahler_cutoff
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
