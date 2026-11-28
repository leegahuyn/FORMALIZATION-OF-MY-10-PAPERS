import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SpectrumFiniteContinuousFactorization
import PrimalitySheafVerification.ManuscriptAudit.FlatTensorStageInjections
import PrimalitySheafVerification.ManuscriptAudit.TensorTripleIncreasingUnion

/-! Finite coefficient functions descend to actual affine double and triple
tensor rings, by first applying stage descent to their subalgebra images. -/

namespace ManuscriptAudit.SpectrumFiniteSectionsInStageImages

open PrimeSpectrum
open scoped TensorProduct

noncomputable section

variable {R B A : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

/-- Factor a genuine finite-valued function through one actual stage ring. -/
theorem factor_of_injective_stage_maps
    (D : ℕ → Type*) [∀ n, CommRing (D n)] [∀ n, Algebra R (D n)]
    (i : ∀ n, D n →ₐ[R] B) (hInj : ∀ n, Function.Injective (i n))
    (hMono : Monotone (fun n => (i n).range))
    (hCover : ∀ b, ∃ n, ∃ x, i n x = b)
    (f : PrimeSpectrum B → A) (hF : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum (D n) → A), Continuous g ∧
      ∀ x, g (comap (i n).toRingHom x) = f x := by
  let U (n : ℕ) := (i n).range
  have hU (b : B) : ∃ n, b ∈ U n := by
    obtain ⟨n, x, hx⟩ := hCover b
    exact ⟨n, x, hx⟩
  obtain ⟨n, g, hg, h⟩ := SpectrumFiniteContinuousFactorization.factor U hMono hU f hF
  let e : D n ≃ₐ[R] U n := AlgEquiv.ofInjective (i n) (hInj n)
  let r : U n →+* D n := e.symm.toRingHom
  have hr (y : U n) : i n (r y) = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  refine ⟨n, g ∘ comap r, hg.comp (continuous_comap r), ?_⟩
  intro x
  have hx : comap r (comap (i n).toRingHom x) = comap (U n).val.toRingHom x := by
    apply PrimeSpectrum.ext
    ext a
    change i n (r a) ∈ x.asIdeal ↔ a.val ∈ x.asIdeal
    rw [hr]
  change g (comap r (comap (i n).toRingHom x)) = f x
  rw [hx]
  exact h x

variable (U : ℕ → Subalgebra R B) (hMono : Monotone U)
  (hCover : ∀ b : B, ∃ n, b ∈ U n)
  (hFlat : ∀ n, Module.Flat R (U n)) [Module.Flat R B]

/-- Every actual finite coefficient section on the double product descends. -/
theorem factor_double (f : PrimeSpectrum (B ⊗[R] B) → A) (hF : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum (U n ⊗[R] U n) → A), Continuous g ∧
      ∀ x, g (comap (TensorSquareIncreasingUnion.stageTensor U n).toRingHom x) = f x :=
  factor_of_injective_stage_maps (fun n => U n ⊗[R] U n)
    (TensorSquareIncreasingUnion.stageTensor U)
    (fun n => by
      letI := hFlat n
      exact FlatTensorStageInjections.stageTensor_injective U n)
    (TensorSquareIncreasingUnion.range_mono U hMono)
    (TensorSquareIncreasingUnion.exists_tensor_stage U hMono hCover) f hF

/-- Every actual finite coefficient section on the triple product descends. -/
theorem factor_triple [Module.Flat R (B ⊗[R] B)]
    (f : PrimeSpectrum ((B ⊗[R] B) ⊗[R] B) → A) (hF : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum ((U n ⊗[R] U n) ⊗[R] U n) → A), Continuous g ∧
      ∀ x, g (comap (FlatTensorStageInjections.stageTriple U n).toRingHom x) = f x :=
  factor_of_injective_stage_maps (fun n => (U n ⊗[R] U n) ⊗[R] U n)
    (FlatTensorStageInjections.stageTriple U)
    (fun n => by
      letI := hFlat n
      exact FlatTensorStageInjections.stageTriple_injective U n)
    (TensorTripleIncreasingUnion.range_mono U hMono)
    (TensorTripleIncreasingUnion.exists_triple_stage U hMono hCover) f hF

end
end ManuscriptAudit.SpectrumFiniteSectionsInStageImages

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SpectrumFiniteSectionsInStageImages.factor_of_injective_stage_maps,
      ``ManuscriptAudit.SpectrumFiniteSectionsInStageImages.factor_double,
      ``ManuscriptAudit.SpectrumFiniteSectionsInStageImages.factor_triple] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
