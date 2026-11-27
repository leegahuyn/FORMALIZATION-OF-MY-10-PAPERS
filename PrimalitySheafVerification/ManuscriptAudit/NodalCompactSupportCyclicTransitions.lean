import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportCyclicDegrees
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCyclicReduction

/-! The genuine finite-coefficient reductions on the compact groups of the split nodal curve. -/

namespace ManuscriptAudit.NodalCompactSupportCyclicTransitions

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (affineOpen projectiveNode)
open NodalSmoothLocusOverlap (smoothOpen)
open OpenComplementRationalPointCohomology (extensionH)
open OpenEtaleCoefficientReduction (reductionH reductionH_surjective reductionH_surjective_of_next_cyclic)

noncomputable section

set_option backward.isDefEq.respectTransparency false
attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]
variable (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a : K)] [NeZero (b : K)]

private instance product_neZero : NeZero ((a * b : ℕ) : K) := ⟨by
  rw [Nat.cast_mul]
  exact mul_ne_zero (NeZero.ne (a : K)) (NeZero.ne (b : K))⟩

private theorem reduction_one_two {U : Scheme.{0}} (j : U ⟶ projectiveNode K) [IsOpenImmersion j]
    (e₂ : ∀ (d : ℕ) [NeZero (d : K)], extensionH j (AddCommGrpCat.of (ZMod d)) 2 ≃+ ZMod d)
    (e₃ : extensionH j (AddCommGrpCat.of (ZMod b)) 3 ≃+ ZMod 1) :
    Function.Surjective (reductionH j a b 1) ∧ Function.Surjective (reductionH j a b 2) := by
  have h₃ : Subsingleton (extensionH j (AddCommGrpCat.of (ZMod b)) 3) :=
    ⟨fun x y ↦ e₃.injective (Subsingleton.elim _ _)⟩
  have h₂ := reductionH_surjective j a b 2 h₃
  exact ⟨reductionH_surjective_of_next_cyclic j a b 1 (e₂ b) (e₂ (a * b)) (e₂ a) h₂, h₂⟩

/-- Genuine coefficient reduction is onto in degrees one and two for compact affine nodal cohomology. -/
theorem affine_reductions_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (reductionH (affineOpen K) a b 1) ∧
      Function.Surjective (reductionH (affineOpen K) a b 2) :=
  reduction_one_two K a b (affineOpen K)
    (fun d i ↦ letI := i; NodalCompactSupportCyclicDegrees.affineEquiv K d h2 2)
    (NodalCompactSupportCyclicDegrees.affineEquiv K b h2 3)

/-- Genuine coefficient reduction is onto in the two positive cyclic degrees of the smooth open. -/
theorem smooth_reductions_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (reductionH (smoothOpen K).ι a b 1) ∧
      Function.Surjective (reductionH (smoothOpen K).ι a b 2) :=
  reduction_one_two K a b (smoothOpen K).ι
    (fun d i ↦ letI := i; NodalCompactSupportCyclicDegrees.smoothEquiv K d h2 2)
    (NodalCompactSupportCyclicDegrees.smoothEquiv K b h2 3)

/-- Genuine reduction is onto in all three cyclic degrees of the proper model. -/
theorem proper_reductions_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (reductionH (𝟙 (projectiveNode K)) a b 0) ∧
      Function.Surjective (reductionH (𝟙 (projectiveNode K)) a b 1) ∧
      Function.Surjective (reductionH (𝟙 (projectiveNode K)) a b 2) := by
  let j := 𝟙 (projectiveNode K)
  have h := reduction_one_two K a b j
    (fun d i ↦ letI := i; NodalCompactSupportCyclicDegrees.properEquiv K d h2 2)
    (NodalCompactSupportCyclicDegrees.properEquiv K b h2 3)
  exact ⟨reductionH_surjective_of_next_cyclic j a b 0
    (NodalCompactSupportCyclicDegrees.properEquiv K b h2 1)
    (NodalCompactSupportCyclicDegrees.properEquiv K (a * b) h2 1)
    (NodalCompactSupportCyclicDegrees.properEquiv K a h2 1) h.1, h⟩

end
end ManuscriptAudit.NodalCompactSupportCyclicTransitions

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportCyclicTransitions.affine_reductions_surjective,
      ``ManuscriptAudit.NodalCompactSupportCyclicTransitions.smooth_reductions_surjective,
      ``ManuscriptAudit.NodalCompactSupportCyclicTransitions.proper_reductions_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
