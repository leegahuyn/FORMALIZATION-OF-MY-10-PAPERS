import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsResolvent

/-! Compact form embeddings give a compact exact resolvent, and the spectral
reciprocity below takes place in the graph of the actual partial operator. -/

namespace ManuscriptAudit.Paper10FriedrichsCompact

open Paper10FriedrichsResolvent

noncomputable section

variable {𝕜 D H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

variable (J : D →L[𝕜] H)

/-- The actual bounded inverse is compact when the form embedding is compact. -/
theorem compact_resolvent (hJ : IsCompactOperator J) : IsCompactOperator (resolvent J) := by
  change IsCompactOperator (J ∘ J.adjoint)
  exact hJ.comp_clm J.adjoint

/-- A nonzero spectral label for the actual partial operator corresponds
to the reciprocal eigenvalue of its canonical bounded inverse. -/
theorem eigenvector_reciprocity (hJ : DenseRange J) (λ : 𝕜) (hλ : λ ≠ 0) (x : H) :
    (x, λ • x) ∈ (realization J).graph ↔ (resolvent J) x = λ⁻¹ • x := by
  rw [realization_graph_iff J hJ, map_smul]
  constructor
  · intro h
    calc
      _ = λ⁻¹ • (λ • (resolvent J) x) := by rw [smul_smul, inv_mul_cancel₀ hλ, one_smul]
      _ = _ := congrArg (fun y : H => λ⁻¹ • y) h
  · intro h
    rw [h, smul_smul, mul_inv_cancel₀ hλ, one_smul]

end
end ManuscriptAudit.Paper10FriedrichsCompact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsCompact.compact_resolvent,
      ``ManuscriptAudit.Paper10FriedrichsCompact.eigenvector_reciprocity] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
