import Lean.Util.CollectAxioms
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! Flat multiplication on the tensor square rules out a flat map from
the one-variable polynomial algebra. -/

namespace ManuscriptAudit.FlatDiagonalPolynomial

open Algebra TensorProduct

noncomputable section

universe u v

variable (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Nontrivial B]

private abbrev P := MvPolynomial Unit K

private abbrev Q := P K ⊗[K] P K

private def coordinateDifference : Q K :=
  (MvPolynomial.X () ⊗ₜ[K] 1) - (1 ⊗ₜ[K] MvPolynomial.X ())

private theorem coordinateDifference_ne_zero : coordinateDifference K ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.tensorEquivSum (R := K) (S := K) (σ := Unit) (ι := Unit)) h
  simp only [coordinateDifference, map_sub, map_zero, MvPolynomial.tensorEquivSum_X_tmul_one,
    MvPolynomial.tensorEquivSum_one_tmul_X] at h'
  exact Sum.inl_ne_inr (MvPolynomial.X_injective (sub_eq_zero.mp h'))

/-- Over a field, flat multiplication on the tensor square excludes a
flat one-variable polynomial parameter in any nontrivial algebra. -/
theorem not_flat_parameter (φ : P K →ₐ[K] B)
    (hμ : (Algebra.TensorProduct.lmul' (S := B) K).Flat) : ¬φ.Flat := by
  intro hφ
  let f : Q K →+* B :=
    (Algebra.TensorProduct.lmul' (S := B) K).toRingHom.comp
      (Algebra.TensorProduct.map φ φ).toRingHom
  have hf : f.Flat := (RingHom.Flat.tensorProductMap hφ hφ).comp hμ
  letI : Algebra (Q K) B := f.toAlgebra
  letI : Module.Flat (Q K) B := hf
  letI : IsDomain (Q K) := (MvPolynomial.tensorEquivSum (R := K) (S := K) (σ := Unit) (ι := Unit)).toRingEquiv.toMulEquiv.isDomain
  let d := coordinateDifference K
  have hreg : IsSMulRegular (Q K) d := by
    intro a b h
    change d * a = d * b at h
    exact mul_left_cancel₀ (coordinateDifference_ne_zero K) h
  have hz : algebraMap (Q K) B d = 0 := by
    change f d = 0
    simp [f, d, coordinateDifference, Algebra.TensorProduct.lmul'_apply_tmul]
  have hregB : IsSMulRegular B (algebraMap (Q K) B d) := hreg.of_flat
  apply zero_ne_one (α := B)
  exact hregB (show (algebraMap (Q K) B d) • (0 : B) =
    (algebraMap (Q K) B d) • (1 : B) by simp [hz])

/-- The obstruction in the ordinary univariate polynomial presentation. -/
theorem not_flat_polynomial_parameter (φ : Polynomial K →ₐ[K] B)
    (hμ : (Algebra.TensorProduct.lmul' (S := B) K).Flat) : ¬φ.Flat := by
  intro hφ
  let e := MvPolynomial.uniqueAlgEquiv K Unit
  have he : e.toRingHom.Flat := RingHom.Flat.of_bijective e.bijective
  exact not_flat_parameter K B (φ.comp e.toAlgHom) hμ (he.comp hφ)

end
end ManuscriptAudit.FlatDiagonalPolynomial

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FlatDiagonalPolynomial.not_flat_parameter,
      ``ManuscriptAudit.FlatDiagonalPolynomial.not_flat_polynomial_parameter] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
