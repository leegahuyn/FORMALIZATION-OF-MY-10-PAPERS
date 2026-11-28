import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SpectrumFiniteSectionsTripleImages

/-! Descent of each genuine finite coefficient section on the triple affine product. -/

namespace ManuscriptAudit.SpectrumFiniteSectionsTriple

open PrimeSpectrum
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R B A : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

local notation "T" => ((B ⊗[R] B) ⊗[R] B)

abbrev images := @SpectrumFiniteSectionsTripleImages.images
abbrev factor_triple_image := @SpectrumFiniteSectionsTripleImages.factor_triple_image

private theorem transport {D C : Type*} [CommRing D] [CommRing C] [Algebra R D] [Algebra R C]
    (j : D →ₐ[R] C) (hj : Function.Injective j) (g : PrimeSpectrum j.range → A)
    (hg : Continuous g) :
    ∃ f : PrimeSpectrum D → A, Continuous f ∧
      ∀ x : PrimeSpectrum C, f (comap j.toRingHom x) = g (comap j.range.val.toRingHom x) := by
  let e : D ≃ₐ[R] j.range := AlgEquiv.ofInjective j hj
  let r : j.range →+* D := e.symm.toRingHom
  have hr (x : j.range) : j (r x) = x.val := congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨g ∘ comap r, hg.comp (continuous_comap r), ?_⟩
  intro x
  have h : comap r (comap j.toRingHom x) = comap j.range.val.toRingHom x := by
    apply PrimeSpectrum.ext
    ext z
    change j (r z) ∈ x.asIdeal ↔ z.val ∈ x.asIdeal
    rw [hr]
  exact congrArg g h

private theorem lift_factorization {C : Type*} [CommRing C] [Algebra R C]
    (D : ℕ → Type*) [∀ n, CommRing (D n)] [∀ n, Algebra R (D n)]
    (j : ∀ n, D n →ₐ[R] C) (hInj : ∀ n, Function.Injective (j n))
    (f : PrimeSpectrum C → A)
    (hFac : ∃ (n : ℕ) (g : PrimeSpectrum (j n).range → A), Continuous g ∧
      ∀ x, g (comap (j n).range.val.toRingHom x) = f x) :
    ∃ (n : ℕ) (g : PrimeSpectrum (D n) → A), Continuous g ∧
      ∀ x, g (comap (j n).toRingHom x) = f x := by
  obtain ⟨n, g, hg, hEq⟩ := hFac
  obtain ⟨φ, hφ, hφEq⟩ := transport (j n) (hInj n) g hg
  exact ⟨n, φ, hφ, fun x ↦ (hφEq x).trans (hEq x)⟩

set_option maxHeartbeats 3000000 in
/-- Injectivity of the literal triple stage maps identifies the factorization with
a function on the actual coordinate ring of that stage. -/
theorem factor_triple (U : ℕ → Subalgebra R B) (hMono : Monotone U)
    (hCover : ∀ b : B, ∃ n, b ∈ U n)
    (hInj : ∀ n, Function.Injective (FlatTensorStageInjections.stageTriple U n))
    (f : PrimeSpectrum T → A) (hF : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum ((U n ⊗[R] U n) ⊗[R] U n) → A), Continuous g ∧
      ∀ x, g (comap (FlatTensorStageInjections.stageTriple U n).toRingHom x) = f x := by
  let D (n : ℕ) := (U n ⊗[R] U n) ⊗[R] U n
  let j (n : ℕ) : D n →ₐ[R] T := FlatTensorStageInjections.stageTriple U n
  letI (n : ℕ) : CommRing (D n) :=
    inferInstanceAs (CommRing ((U n ⊗[R] U n) ⊗[R] U n))
  letI (n : ℕ) : Algebra R (D n) :=
    inferInstanceAs (Algebra R ((U n ⊗[R] U n) ⊗[R] U n))
  exact lift_factorization (R := R) (C := T) D j hInj f
    (SpectrumFiniteSectionsTripleImages.factor_triple_image U hMono hCover f hF)

end
end ManuscriptAudit.SpectrumFiniteSectionsTriple

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SpectrumFiniteSectionsTriple.factor_triple] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
