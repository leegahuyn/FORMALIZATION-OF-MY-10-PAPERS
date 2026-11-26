import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.InvolutionTensorComparison
import PrimalitySheafVerification.ManuscriptAudit.NodalAffinePresentation
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCover

/-!
# The crossed algebra has the actual two-copy torsor comparison

For the two anti-invariant elements (t,-t) and (x,-x), where x=t²-1,
the coefficients 1-x and 1 give a partition of unity by squares.
-/

namespace ManuscriptAudit.NodalSwapCoverTorsor

open NodalConductor NodalSwapCover NodalAffinePresentation Polynomial
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]

private abbrev A := coordinates K
private abbrev T := Cover K

private def skewT : T K :=
  ⟨(X, -X), by
    change (X : K[X]).eval 1 = (-(X : K[X])).eval (-1) ∧
      (X : K[X]).eval (-1) = (-(X : K[X])).eval 1
    simp⟩

private def skewX : T K :=
  ⟨(x K, -(x K)), by
    change (x K).eval 1 = (-(x K)).eval (-1) ∧ (x K).eval (-1) = (-(x K)).eval 1
    simp [x]⟩

private theorem skewT_anti : swap K (skewT K) = -(skewT K) :=
  Subtype.ext (Prod.ext rfl (neg_neg (X : K[X])).symm)

private theorem skewX_anti : swap K (skewX K) = -(skewX K) :=
  Subtype.ext (Prod.ext rfl (neg_neg (x K)).symm)

private def weight : T K :=
  algebraMap (A K) (T K) (1 - nodeX K)

private theorem partition : weight K * (skewT K) ^ 2 + (skewX K) ^ 2 = 1 := by
  apply Subtype.ext
  change (crossedPairs K).val (weight K * (skewT K) ^ 2 + (skewX K) ^ 2) =
    (crossedPairs K).val (1 : T K)
  simp only [map_add, map_mul, map_pow, map_one]
  change ((1 - x K) * (X : K[X]) ^ 2 + (x K) ^ 2,
    (1 - x K) * (-(X : K[X])) ^ 2 + (-(x K)) ^ 2) = (1, 1)
  apply Prod.ext <;> change _ = (1 : K[X]) <;> unfold x <;> ring

private def half (K : Type u) [Field K] : T K :=
  algebraMap (A K) (T K) (algebraMap K (A K) ((2 : K)⁻¹))

private theorem half_add_half (h2 : (2 : K) ≠ 0) : half K + half K = 1 := by
  have h : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  unfold half
  rw [← map_add, ← map_add, h, map_one, map_one]

private theorem comparison_bijective (h2 : (2 : K) ≠ 0) :
    Function.Bijective (InvolutionTensorComparison.comparison (A K) (T K) (swap K)) :=
  InvolutionTensorComparison.comparison_bijective (A K) (T K) (swap K) (swap_twice K)
    (fun z hz => (swap_fixed_iff_from_node K h2 z).mp hz)
    (half K) (weight K) (skewT K) (skewX K)
    ((swap_fixed_iff_from_node K h2 (half K)).mpr ⟨_, rfl⟩) (half_add_half K h2)
    ((swap_fixed_iff_from_node K h2 (weight K)).mpr ⟨_, rfl⟩)
    (skewT_anti K) (skewX_anti K) (partition K)

/-- The canonical map of the actual involution identifies the tensor algebra with two copies. -/
def torsorEquiv (h2 : (2 : K) ≠ 0) : (T K ⊗[A K] T K) ≃ₐ[T K] (T K × T K) :=
  AlgEquiv.ofBijective (InvolutionTensorComparison.comparison (A K) (T K) (swap K))
    (comparison_bijective K h2)

theorem torsorEquiv_tmul (h2 : (2 : K) ≠ 0) (a b : T K) :
    torsorEquiv K h2 (a ⊗ₜ[A K] b) = (a * b, a * swap K b) :=
  InvolutionTensorComparison.comparison_tmul (A K) (T K) (swap K) a b

end

end ManuscriptAudit.NodalSwapCoverTorsor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCoverTorsor.torsorEquiv,
        ``ManuscriptAudit.NodalSwapCoverTorsor.torsorEquiv_tmul] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
