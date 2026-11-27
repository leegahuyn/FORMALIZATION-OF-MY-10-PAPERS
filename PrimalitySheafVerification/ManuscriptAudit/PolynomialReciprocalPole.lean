import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Module.Cardinality

/-! A nonzero polynomial reciprocal has no finite continuous extension at a denominator root. -/

namespace ManuscriptAudit.PolynomialReciprocalPole

open Filter Topology Polynomial

theorem no_continuous_reciprocal_extension (P : ℂ[X]) (hP : P ≠ 0) {z₀ : ℂ}
    (hz₀ : P.eval z₀ = 0) :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g z₀ ∧
      ∀ᶠ z in 𝓝[{z : ℂ | P.eval z ≠ 0}] z₀, g z = (P.eval z)⁻¹ := by
  rintro ⟨g, hg, hEq⟩
  let S : Set ℂ := {z | P.eval z ≠ 0}
  have hRoots : {z : ℂ | P.IsRoot z}.Finite := Polynomial.finite_setOf_isRoot hP
  have hdense : Dense S := hRoots.countable.dense_compl ℝ
  letI : NeBot (𝓝[S] z₀) := mem_closure_iff_nhdsWithin_neBot.mp (hdense z₀)
  have hOne : (fun _ : ℂ => (1 : ℂ)) =ᶠ[𝓝[S] z₀] fun z => g z * P.eval z := by
    filter_upwards [hEq, self_mem_nhdsWithin] with z hgZ hz
    change P.eval z ≠ 0 at hz
    change (1 : ℂ) = g z * P.eval z
    rw [hgZ, inv_mul_cancel₀ hz]
  have hOneLim : Tendsto (fun z => g z * P.eval z) (𝓝[S] z₀) (𝓝 1) :=
    tendsto_const_nhds.congr' hOne
  have hCont : ContinuousAt (fun z => g z * P.eval z) z₀ :=
    hg.mul P.continuousAt
  have hZeroLim : Tendsto (fun z => g z * P.eval z) (𝓝[S] z₀) (𝓝 0) := by
    simpa only [hz₀, mul_zero] using hCont.mono_left nhdsWithin_le_nhds
  exact one_ne_zero (tendsto_nhds_unique hOneLim hZeroLim)

end ManuscriptAudit.PolynomialReciprocalPole

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.PolynomialReciprocalPole.no_continuous_reciprocal_extension
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
