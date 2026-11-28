import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SpectrumFiniteSectionsInStageImages
import PrimalitySheafVerification.ManuscriptAudit.TensorTripleIncreasingUnion

/-! Descent of each genuine finite coefficient section on the triple affine product. -/

namespace ManuscriptAudit.SpectrumFiniteSectionsTripleImages

open PrimeSpectrum
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R B A : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

local notation "T" => ((B ⊗[R] B) ⊗[R] B)

abbrev images (U : ℕ → Subalgebra R B) : ℕ → Subalgebra R T :=
  fun n => (FlatTensorStageInjections.stageTriple U n).range

set_option maxHeartbeats 1900000 in
/-- Each finite discrete section already factors through the image of one literal
triple tensor stage. -/
theorem factor_triple_image (U : ℕ → Subalgebra R B) (hMono : Monotone U)
    (hCover : ∀ b : B, ∃ n, b ∈ U n)
    (f : PrimeSpectrum T → A) (hF : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum (images U n) → A), Continuous g ∧
      ∀ x, g (comap (images U n).val.toRingHom x) = f x := by
  have hM : Monotone (images U) := TensorTripleIncreasingUnion.range_mono U hMono
  have hC (b' : T) : ∃ n, b' ∈ images U n := by
    obtain ⟨n, w, hw⟩ := TensorTripleIncreasingUnion.exists_triple_stage U hMono hCover b'
    exact ⟨n, w, hw⟩
  exact SpectrumFiniteContinuousFactorization.factor (images U) hM hC f hF

end
end ManuscriptAudit.SpectrumFiniteSectionsTripleImages

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SpectrumFiniteSectionsTripleImages.factor_triple_image] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
