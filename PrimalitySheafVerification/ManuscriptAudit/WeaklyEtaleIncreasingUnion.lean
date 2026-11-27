import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.FlatIncreasingUnion
import PrimalitySheafVerification.ManuscriptAudit.TensorDiagonalFlatIncreasingUnion

/-! Exhaustive increasing unions of actual étale affine algebras give
weakly étale morphisms, and finite-stage integrality gives surjectivity. -/

namespace ManuscriptAudit.WeaklyEtaleIncreasingUnion

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (U : ℕ → Subalgebra R B)
variable (hMono : Monotone U) (hCover : ∀ b : B, ∃ n, b ∈ U n)

private abbrev f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R B))

include hMono hCover in
/-- The native affine scheme of an exhaustive increasing union of étale
subalgebras is weakly étale over the affine base. -/
theorem weaklyEtale (hEtale : ∀ n, Algebra.Etale R (U n)) : WeaklyEtale (f (R := R) (B := B)) := by
  have hFlat : Module.Flat R B := by
    apply FlatIncreasingUnion.flat_of_exhaustion (fun n ↦ (U n).toSubmodule) hMono hCover
    intro n
    letI := hEtale n
    exact inferInstanceAs (Module.Flat R (U n))
  letI : Flat (f (R := R) (B := B)) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hFlat)
  let μ := CommRingCat.ofHom ((Algebra.TensorProduct.lmul' (S := B) R).toRingHom)
  letI : Flat (Spec.map μ) := Flat.SpecMap_iff.mpr
    (TensorDiagonalFlatIncreasingUnion.multiplication_flat U hMono hCover hEtale)
  refine ⟨inferInstance, ?_⟩
  change Flat (CategoryTheory.Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R B))))
  rw [AlgebraicGeometry.diagonal_SpecMap]
  infer_instance

include hCover in
/-- If all the stages are integral and the base inclusion is injective,
the actual weakly étale map of affine schemes is surjective. -/
theorem surjective (hIntegral : ∀ n, Algebra.IsIntegral R (U n))
    (hInj : Function.Injective (algebraMap R B)) : Surjective (f (R := R) (B := B)) := by
  letI : Algebra.IsIntegral R B := ⟨by
    intro x
    obtain ⟨n, hn⟩ := hCover x
    letI := hIntegral n
    exact (Algebra.IsIntegral.isIntegral (R := R) (⟨x, hn⟩ : U n)).map (U n).val⟩
  letI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hInj
  rw [AlgebraicGeometry.surjective_iff]
  exact Algebra.IsIntegral.comap_surjective R B

end
end ManuscriptAudit.WeaklyEtaleIncreasingUnion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleIncreasingUnion.weaklyEtale,
      ``ManuscriptAudit.WeaklyEtaleIncreasingUnion.surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
