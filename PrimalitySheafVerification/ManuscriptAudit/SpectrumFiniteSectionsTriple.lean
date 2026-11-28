import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SpectrumFiniteSectionsInStageImages
import PrimalitySheafVerification.ManuscriptAudit.TensorTripleIncreasingUnion

/-! Descent of each genuine finite coefficient section on the triple affine product. -/

namespace ManuscriptAudit.SpectrumFiniteSectionsTriple

open PrimeSpectrum
open scoped TensorProduct

noncomputable section

variable {R B A : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

set_option maxHeartbeats 6000000 in
theorem factor_triple (U : ℕ → Subalgebra R B) (hMono : Monotone U)
    (hCover : ∀ b : B, ∃ n, b ∈ U n) (hFlat : ∀ n, Module.Flat R (U n))
    [Module.Flat R B] [Module.Flat R (B ⊗[R] B)]
    (f : PrimeSpectrum ((B ⊗[R] B) ⊗[R] B) → A) (hF : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum ((U n ⊗[R] U n) ⊗[R] U n) → A), Continuous g ∧
      ∀ x, g (comap (FlatTensorStageInjections.stageTriple U n).toRingHom x) = f x := by
  let j (n : ℕ) : ((U n ⊗[R] U n) ⊗[R] U n) →ₐ[R] ((B ⊗[R] B) ⊗[R] B) :=
    FlatTensorStageInjections.stageTriple U n
  have hInj (n : ℕ) : Function.Injective (j n) := by
    letI := hFlat n
    exact FlatTensorStageInjections.stageTriple_injective U n
  have hM : Monotone (fun n => (j n).range) := TensorTripleIncreasingUnion.range_mono U hMono
  have hC : ∀ b', ∃ n, ∃ y, j n y = b' :=
    TensorTripleIncreasingUnion.exists_triple_stage U hMono hCover
  exact SpectrumFiniteSectionsInStageImages.factor_of_injective_stage_maps
    (R := R) (B := (B ⊗[R] B) ⊗[R] B) (fun n => (U n ⊗[R] U n) ⊗[R] U n)
    j hInj hM hC f hF

end
end ManuscriptAudit.SpectrumFiniteSectionsTriple

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SpectrumFiniteSectionsTriple.factor_triple
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
