import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compression of a bounded potential to a Hilbert subspace

A real bounded pointwise potential need not leave a gauge slice invariant.
For a realized closed Hilbert slice, the orthogonal compression is a
bounded self-adjoint operator when the ambient potential is, and its
form on the slice is the ambient form.
-/

namespace ManuscriptAudit.CoulombPotentialCompression

noncomputable section

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable (U : Submodule 𝕜 H) [CompleteSpace U]

/-- Include the vector into the ambient space, apply the potential, and
then project orthogonally back to the slice. -/
def compressPotential (V : H →L[𝕜] H) : U →L[𝕜] U :=
  U.orthogonalProjectionOnto ∘L V ∘L U.subtypeL

theorem compressPotential_norm_le (V : H →L[𝕜] H) :
    ‖compressPotential U V‖ ≤ ‖V‖ := by
  refine (compressPotential U V).opNorm_le_bound (norm_nonneg _) fun x => ?_
  change ‖U.orthogonalProjectionOnto (V (x : H))‖ ≤ ‖V‖ * ‖(x : H)‖
  exact (U.norm_orthogonalProjectionOnto_apply_le _).trans (V.le_opNorm _)

variable [CompleteSpace H]

theorem compressPotential_selfAdjoint {V : H →L[𝕜] H} (hV : IsSelfAdjoint V) :
    IsSelfAdjoint (compressPotential U V) := by
  unfold compressPotential
  rw [← U.adjoint_subtypeL]
  exact hV.adjoint_conj U.subtypeL

/-- Hence the compressed operator realizes the original potential's
restricted quadratic form without asking for invariance of the slice. -/
theorem compressPotential_inner (V : H →L[𝕜] H) (x y : U) :
    inner 𝕜 (compressPotential U V x) y = inner 𝕜 (V (x : H)) (y : H) := by
  change inner 𝕜 (U.orthogonalProjectionOnto (V (x : H))) y =
    inner 𝕜 (V (x : H)) (U.subtypeL y)
  rw [← U.adjoint_subtypeL]
  exact ContinuousLinearMap.adjoint_inner_left U.subtypeL y (V (x : H))

omit [CompleteSpace H] in
theorem compressPotential_eq_of_image_mem (V : H →L[𝕜] H) (x : U) (hx : V (x : H) ∈ U) :
    (compressPotential U V x : H) = V (x : H) := by
  let y : U := ⟨V (x : H), hx⟩
  change (U.orthogonalProjectionOnto (y : H) : H) = y
  exact congrArg (fun z : U => (z : H)) (U.orthogonalProjectionOnto_mem_subspace_eq_self y)

end

end ManuscriptAudit.CoulombPotentialCompression

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombPotentialCompression.compressPotential_norm_le,
      ``ManuscriptAudit.CoulombPotentialCompression.compressPotential_selfAdjoint,
      ``ManuscriptAudit.CoulombPotentialCompression.compressPotential_inner,
      ``ManuscriptAudit.CoulombPotentialCompression.compressPotential_eq_of_image_mem] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
