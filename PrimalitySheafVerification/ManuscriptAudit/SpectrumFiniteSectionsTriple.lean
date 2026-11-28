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

local notation "T" => ((B ⊗[R] B) ⊗[R] B)

def images (U : ℕ → Subalgebra R B) : ℕ → Subalgebra R T :=
  fun n => (FlatTensorStageInjections.stageTriple U n).range

set_option maxHeartbeats 550000 in
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

set_option maxHeartbeats 550000 in
/-- Injectivity of the literal triple stage maps identifies the factorization with
a function on the actual coordinate ring of that stage. -/
theorem factor_triple (U : ℕ → Subalgebra R B) (hMono : Monotone U)
    (hCover : ∀ b : B, ∃ n, b ∈ U n)
    (hInj : ∀ n, Function.Injective (FlatTensorStageInjections.stageTriple U n))
    (f : PrimeSpectrum T → A) (hF : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum ((U n ⊗[R] U n) ⊗[R] U n) → A), Continuous g ∧
      ∀ x, g (comap (FlatTensorStageInjections.stageTriple U n).toRingHom x) = f x := by
  obtain ⟨n, g, hg, h⟩ := factor_triple_image U hMono hCover f hF
  let j := FlatTensorStageInjections.stageTriple U n
  let e : ((U n ⊗[R] U n) ⊗[R] U n) ≃ₐ[R] images U n :=
    AlgEquiv.ofInjective j (hInj n)
  let r := e.symm.toRingHom
  have hr (y : images U n) : j (r y) = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  refine ⟨n, g ∘ comap r, hg.comp (continuous_comap r), ?_⟩
  intro x
  have hx : comap r (comap j.toRingHom x) = comap (images U n).val.toRingHom x := by
    apply PrimeSpectrum.ext
    ext a
    change j (r a) ∈ x.asIdeal ↔ a.val ∈ x.asIdeal
    rw [hr]
  change g (comap r (comap j.toRingHom x)) = f x
  rw [hx]
  exact h x

end
end ManuscriptAudit.SpectrumFiniteSectionsTriple

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SpectrumFiniteSectionsTriple.factor_triple_image,
      ``ManuscriptAudit.SpectrumFiniteSectionsTriple.factor_triple] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
