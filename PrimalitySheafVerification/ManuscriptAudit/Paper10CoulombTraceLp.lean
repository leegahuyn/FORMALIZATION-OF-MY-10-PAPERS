import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10CuspProfileHilbert
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombTraceClosure

/-! Smooth zero-Dirichlet horizontal co-closed forms do not constitute
a closed slice in the actual L² space of horizontal cusp profiles. -/

namespace ManuscriptAudit.Paper10CoulombTraceLp

open Paper10CuspProfileHilbert Paper10CoulombTraceClosure
open scoped ContDiff

noncomputable section

/-- Each element is represented by a smooth horizontal form with zero
full trace at the upper horocycle. The width factor is constant. -/
def zeroTrace : Set ProfileL2 :=
  {z | ∃ f : ℝ → ℝ, ∃ hf : ContDiff ℝ ∞ f, f 6 = 0 ∧ z = vector f hf.continuous}

private abbrev hLimit := (profiles_smooth 0).1
def limitVector : ProfileL2 := vector limitProfile hLimit.continuous

theorem limit_mem_closure : limitVector ∈ closure zeroTrace := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := native_arbitrarily_close (2 * ε^2) (by positivity)
  let f := approximation n
  have hf : ContDiff ℝ ∞ f := (profiles_smooth n).2
  let z := vector f hf.continuous
  have hz : z ∈ zeroTrace := by
    have ht : f 6 = 0 := approximate_zero_near_trace n 6
      (sub_le_self _ (by positivity))
    exact ⟨f, hf, ht, rfl⟩
  refine ⟨z, hz, ?_⟩
  have hn' : 2 * ‖limitVector - z‖^2 < 2 * ε^2 := by
    change 2 * ‖vector limitProfile hLimit.continuous - vector f hf.continuous‖^2 < _
    rw [distance_squared]
    exact hn
  rw [dist_eq_norm_sub]
  by_contra! hc
  have hN := norm_nonneg (limitVector - z)
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (add_nonneg hN hε.le)]

theorem limit_not_mem : limitVector ∉ zeroTrace := by
  rintro ⟨f, hf, ht, he⟩
  have h := trace_eq limitProfile f hLimit.continuous hf.continuous he
  rw [limit_nonzero_trace, ht] at h
  norm_num at h

theorem zeroTrace_not_closed : ¬ IsClosed zeroTrace := by
  intro h
  exact limit_not_mem (h.closure_eq ▸ limit_mem_closure)

end
end ManuscriptAudit.Paper10CoulombTraceLp

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CoulombTraceLp.limit_mem_closure,
      ``ManuscriptAudit.Paper10CoulombTraceLp.limit_not_mem,
      ``ManuscriptAudit.Paper10CoulombTraceLp.zeroTrace_not_closed] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
