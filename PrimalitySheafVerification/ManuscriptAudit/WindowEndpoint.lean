import Mathlib.Algebra.Group.Indicator
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Closed-window majorant in Paper 10

The proof sketch of Proposition 4.27 on physical PDF p. 500 uses a smooth
majorant supported in `[T−1,T+1]`. Corollary 4.28 chooses the test function
above the indicator of `[T,T+1]`. The two pointwise specifications cannot
hold for the same test function. The obstruction is independent of the
spectral data. It leaves the conditional Weyl-to-window counting implication
with a test on a wider support available for separate verification.
-/

namespace ManuscriptAudit.WindowEndpoint

open Set

private theorem continuous_eq_zero_at_upper_support_endpoint {B : ℝ → ℝ} {b : ℝ}
    (hB : Continuous B) (hsupp : Function.support B ⊆ Iic b) : B b = 0 := by
  have hz : Ioi b ⊆ B ⁻¹' ({0} : Set ℝ) := by
    intro t ht
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have htSupport : t ∈ Function.support B := Function.mem_support.mpr hne
    have htLe : t ≤ b := Set.mem_Iic.mp (hsupp htSupport)
    exact (not_lt_of_ge htLe) (Set.mem_Ioi.mp ht)
  have hclosed : IsClosed (B ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hB
  have hb : b ∈ closure (Ioi b) := by
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  exact Set.mem_singleton_iff.mp (closure_minimal hz hclosed hb)

/-- The compact support and closed-window indicator conditions on p. 500
are incompatible even with continuity in place of smoothness. -/
theorem no_printed_closed_window_majorant (T : ℝ) :
    ¬ ∃ Φ B : ℝ → ℝ,
      Continuous B ∧
      Function.support B ⊆ Icc (T - 1) (T + 1) ∧
      (∀ t : ℝ, Φ t ≤ B t) ∧
      (∀ t : ℝ, Set.indicator (Icc T (T + 1)) (fun _ : ℝ => (1 : ℝ)) t ≤ Φ t) := by
  rintro ⟨Φ, B, hB, hsupp, hmajor, hind⟩
  have hzero : B (T + 1) = 0 :=
    continuous_eq_zero_at_upper_support_endpoint hB (fun _ ht => (hsupp ht).2)
  have hmem : T + 1 ∈ Icc T (T + 1) :=
    ⟨le_add_of_nonneg_right zero_le_one, le_rfl⟩
  have hleft : (1 : ℝ) ≤ Φ (T + 1) := by
    simpa only [Set.indicator_of_mem hmem] using hind (T + 1)
  have hcontra := hleft.trans (hmajor (T + 1))
  rw [hzero] at hcontra
  exact (not_le_of_gt zero_lt_one) hcontra

end ManuscriptAudit.WindowEndpoint

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WindowEndpoint.no_printed_closed_window_majorant
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
