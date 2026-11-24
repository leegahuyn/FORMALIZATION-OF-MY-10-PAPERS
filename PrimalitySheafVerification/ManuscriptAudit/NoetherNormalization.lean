import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# The affine plane cannot be finite over the affine line

Paper 7, pp. 269–270, uses a finite map to the line in the printed
Noether normalization argument for arbitrary finite-type fibers.
Already over a field, a finite morphism from the affine plane to the
affine line is impossible by incomparability and Krull dimension.
-/

namespace ManuscriptAudit.NoetherNormalization

open AlgebraicGeometry CategoryTheory

theorem ringKrullDim_le_of_integral (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro x y h
  letI : x.asIdeal.IsPrime := x.isPrime
  change x.asIdeal < y.asIdeal at h
  change x.asIdeal.comap (algebraMap R S) < y.asIdeal.comap (algebraMap R S)
  exact Ideal.IsIntegral.comap_lt_comap h

theorem paper7_no_finite_affine_plane_ring_map (K : Type*) [Field K]
    (f : Polynomial K →+* MvPolynomial (Fin 2) K) : ¬ f.Finite := by
  intro hf
  letI : Algebra (Polynomial K) (MvPolynomial (Fin 2) K) := f.toAlgebra
  letI : Module.Finite (Polynomial K) (MvPolynomial (Fin 2) K) := hf
  letI : Algebra.IsIntegral (Polynomial K) (MvPolynomial (Fin 2) K) :=
    Algebra.IsIntegral.of_finite _ _
  have h := ringKrullDim_le_of_integral (Polynomial K) (MvPolynomial (Fin 2) K)
  have h₂ : ringKrullDim (MvPolynomial (Fin 2) K) = 2 := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  have h₁ : ringKrullDim (Polynomial K) = 1 := by
    simp [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rw [h₂, h₁] at h
  exact absurd h (by decide)

/-- The obstruction concerns the actual affine scheme morphism, with
no assumption of dominance. -/
theorem paper7_no_finite_affine_plane_to_line (K : Type*) [Field K]
    (f : Spec (CommRingCat.of (MvPolynomial (Fin 2) K)) ⟶
      Spec (CommRingCat.of (Polynomial K))) : ¬ IsFinite f := by
  intro hf
  obtain ⟨g, rfl⟩ := Spec.map_surjective f
  exact paper7_no_finite_affine_plane_ring_map K g.hom ((IsFinite.SpecMap_iff g).1 hf)

end ManuscriptAudit.NoetherNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.NoetherNormalization.ringKrullDim_le_of_integral,
      ``ManuscriptAudit.NoetherNormalization.paper7_no_finite_affine_plane_ring_map,
      ``ManuscriptAudit.NoetherNormalization.paper7_no_finite_affine_plane_to_line] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
