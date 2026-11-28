import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.PicardGroup

/-! Finite affine Weierstrass quotients and the degree-one contribution of
a rational closed point to the quotient of an invertible ideal. -/

namespace ManuscriptAudit.WeierstrassIdealDegree

open Polynomial WeierstrassCurve.Affine Module TensorProduct AlgebraTensorModule
open scoped BigOperators

noncomputable section

universe u
variable {K : Type u} [Field K]

/-- An invertible ideal has a one-dimensional fiber at a rational maximal ideal. -/
theorem invertible_ideal_rational_fiber {R : Type u} [CommRing R] [Algebra K R]
    (I P : Ideal R) [Module.Invertible R I] [P.IsMaximal]
    (e : (R ⧸ P) ≃ₐ[K] K) :
    Module.finrank K (I ⧸ (P • (⊤ : Submodule R I))) = 1 := by
  let F := R ⧸ P
  letI : Field F := Ideal.Quotient.field P
  let V := F ⊗[R] I
  let h : Nonempty (V ≃ₗ[F] F) :=
    (Module.Invertible.free_iff_linearEquiv (R := F) (M := V)).mp inferInstance
  let eR : (I ⧸ (P • (⊤ : Submodule R I))) ≃ₗ[R] F :=
    (TensorProduct.quotTensorEquivQuotSMul I P).symm.trans (h.some.restrictScalars R)
  exact (((eR.restrictScalars K).trans e.toLinearEquiv).finrank_eq).trans (Module.finrank_self K)

/-- Multiplying an invertible ideal by a rational maximal ideal increases
the ground-field dimension of the quotient by exactly one. -/
theorem quotient_degree_mul_rational {R : Type u} [CommRing R] [Algebra K R]
    (I P : Ideal R) [Module.Invertible R I] [P.IsMaximal]
    [Module.Finite K (R ⧸ (P * I))] (e : (R ⧸ P) ≃ₐ[K] K) :
    Module.finrank K (R ⧸ (P * I)) = Module.finrank K (R ⧸ I) + 1 := by
  let Q : Ideal R := P * I
  have hQI : Q ≤ I := Ideal.mul_le_left
  let f : (R ⧸ Q) →ₗ[R] (R ⧸ I) := Submodule.factor hQI
  let g : I →ₗ[R] (R ⧸ Q) := Q.mkQ.comp I.subtype
  have hgKer : g.ker = P • (⊤ : Submodule R I) := by
    change (Q.mkQ.comp I.subtype).ker = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    change Submodule.comap I.subtype (P * I) = _
    rw [← Ideal.smul_eq_mul, Submodule.comap_smul'' I.subtype_injective
      (by rw [Submodule.range_subtype]), Submodule.comap_subtype_self]
  have hExact : g.range = f.ker := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      change f (Q.mkQ x.val) = 0
      rw [show f (Q.mkQ x.val) = I.mkQ x.val from rfl]
      exact (Submodule.Quotient.mk_eq_zero I).mpr x.property
    · intro ha
      obtain ⟨x, rfl⟩ := Q.mkQ_surjective a
      have hx : I.mkQ x = 0 := ha
      exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero I).mp hx⟩, rfl⟩
  let eKer : (I ⧸ (P • (⊤ : Submodule R I))) ≃ₗ[R] f.ker := by
    rw [← hgKer]
    exact g.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hExact)
  let fK := f.restrictScalars K
  have hKerDim : Module.finrank K fK.ker = 1 := by
    change Module.finrank K f.ker = 1
    exact (eKer.restrictScalars K).finrank_eq.symm.trans (invertible_ideal_rational_fiber I P e)
  have hf : Function.Surjective fK := Submodule.factor_surjective hQI
  have hRangeDim : Module.finrank K fK.range = Module.finrank K (R ⧸ I) := by
    have h : Function.Surjective fK.range.subtype := by
      intro x
      exact ⟨⟨x, hf x⟩, rfl⟩
    exact (LinearEquiv.ofBijective fK.range.subtype ⟨fK.range.subtype_injective, h⟩).finrank_eq
  have h := (LinearMap.finrank_range_add_finrank_ker fK).symm
  rwa [hRangeDim, hKerDim] at h

variable (W : WeierstrassCurve.Affine K)

/-- Every nonzero ideal of the literal affine coordinate ring has a
finite-dimensional quotient over the ground field. -/
theorem nonzero_quotient_finite (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    Module.Finite K (W.CoordinateRing ⧸ I) := by
  let b := CoordinateRing.basis W
  let e := Ideal.quotientEquivDirectSum K b hI
  letI (i : Fin 2) : Module.Finite K (K[X] ⧸ Ideal.span ({I.smithCoeffs b hI i} : Set K[X])) :=
    PowerBasis.finite (AdjoinRoot.powerBasis (I.smithCoeffs_ne_zero b hI i))
  let M (i : Fin 2) := K[X] ⧸ Ideal.span ({I.smithCoeffs b hI i} : Set K[X])
  let e' := DirectSum.linearEquivFunOnFintype K (Fin 2) M
  let E := e.trans e'
  exact Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective

end

end ManuscriptAudit.WeierstrassIdealDegree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassIdealDegree.invertible_ideal_rational_fiber,
      ``ManuscriptAudit.WeierstrassIdealDegree.quotient_degree_mul_rational,
      ``ManuscriptAudit.WeierstrassIdealDegree.nonzero_quotient_finite] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
