import Lean.Util.CollectAxioms
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.NodalConductor

/-! The normalization of the split affine node is the polynomial line. -/

namespace ManuscriptAudit.NodalNormalization

open Polynomial NodalConductor

noncomputable section

variable (K : Type*) [Field K]

private theorem span_one_X (h2 : (2 : K) ≠ 0) :
    Submodule.span (coordinates K) ({1, X} : Set K[X]) = ⊤ := by
  apply top_unique
  intro f _
  let S := Submodule.span (coordinates K) ({1, X} : Set K[X])
  let c := (f.eval 1 - f.eval (-1)) / 2
  let a : coordinates K := ⟨f - C c * X, by
    rw [coordinates_eq_equalBranchValues K h2, mem_equalBranchValues]
    simp [c]
    field_simp <;> ring⟩
  let b : coordinates K := ⟨C c, by
    rw [Polynomial.C_eq_algebraMap]
    exact (coordinates K).algebraMap_mem _⟩
  have h₁ : (1 : K[X]) ∈ S := Submodule.subset_span (by simp)
  have hX : (X : K[X]) ∈ S := Submodule.subset_span (by simp)
  have hf : a • (1 : K[X]) + b • (X : K[X]) = f := by
    change (f - C c * X) * 1 + C c * X = f
    rw [mul_one, sub_add_cancel]
  rw [← hf]
  exact S.add_mem (S.smul_mem a h₁) (S.smul_mem b hX)

theorem normalization_finite (h2 : (2 : K) ≠ 0) :
    Module.Finite (coordinates K) K[X] := by
  classical
  refine ⟨⟨{1, X}, ?_⟩⟩
  simpa only [Finset.coe_insert, Finset.coe_singleton] using span_one_X K h2

private theorem x_ne_zero : x K ≠ 0 := by
  intro e
  have hc := congrArg constantCoeff e
  simpa [x] using hc

theorem common_fraction_field : IsFractionRing (coordinates K) (FractionRing K[X]) := by
  refine IsFractionRing.of_field (coordinates K) (FractionRing K[X]) ?_
  intro q
  obtain ⟨f, g, _, hq⟩ := IsFractionRing.div_surjective K[X] q
  let a : coordinates K := ⟨x K * f, x_mul_mem_coordinates K f⟩
  let b : coordinates K := ⟨x K * g, x_mul_mem_coordinates K g⟩
  have hx : algebraMap K[X] (FractionRing K[X]) (x K) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (FractionRing K[X]))).mpr (x_ne_zero K)
  refine ⟨a, b, ?_⟩
  change q = algebraMap K[X] (FractionRing K[X]) (x K * f) /
    algebraMap K[X] (FractionRing K[X]) (x K * g)
  simpa only [map_mul, mul_div_mul_left _ _ hx] using hq.symm

theorem polynomial_is_integral_closure (h2 : (2 : K) ≠ 0) :
    IsIntegralClosure K[X] (coordinates K) (FractionRing K[X]) := by
  classical
  letI : GCDMonoid K[X] := EuclideanDomain.gcdMonoid _
  letI : Module.Finite (coordinates K) K[X] := normalization_finite K h2
  letI : Algebra.IsIntegral (coordinates K) K[X] := Algebra.IsIntegral.of_finite _ _
  exact IsIntegralClosure.of_isIntegrallyClosed K[X] (coordinates K) (FractionRing K[X])

end
end ManuscriptAudit.NodalNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalization.normalization_finite,
      ``ManuscriptAudit.NodalNormalization.common_fraction_field,
      ``ManuscriptAudit.NodalNormalization.polynomial_is_integral_closure] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
