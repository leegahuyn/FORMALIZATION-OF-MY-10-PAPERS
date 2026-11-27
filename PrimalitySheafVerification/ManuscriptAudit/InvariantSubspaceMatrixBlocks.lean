import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection

/-! Adapted bases identify the lower blocks with the quotient action. -/

namespace ManuscriptAudit.InvariantSubspaceMatrixBlocks

open Module

noncomputable section

variable {K V ι τ : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {U W : Submodule K V} (h : IsCompl U W)

private def sumEquiv : (U × (V ⧸ U)) ≃ₗ[K] V :=
  ((LinearEquiv.refl K U).prodCongr (U.quotientEquivOfIsCompl W h)).trans
    (U.prodEquivOfIsCompl W h)

private theorem quotient_sumEquiv (x : U × (V ⧸ U)) :
    U.mkQ (sumEquiv h x) = x.2 := by
  change U.mkQ ((x.1 : V) + ((U.quotientEquivOfIsCompl W h x.2 : W) : V)) = _
  rw [map_add]
  have hzero : U.mkQ x.1 = 0 := by
    rw [← LinearMap.mem_ker, U.ker_mkQ]
    exact x.1.property
  rw [hzero, zero_add]
  exact U.mk_quotientEquivOfIsCompl_apply h x.2

def adaptedBasis (a : Basis ι K U) (b : Basis τ K (V ⧸ U)) : Basis (ι ⊕ τ) K V :=
  (a.prod b).map (sumEquiv h)

theorem adaptedBasis_quotient_left (a : Basis ι K U) (b : Basis τ K (V ⧸ U)) (i : ι) :
    U.mkQ (adaptedBasis h a b (Sum.inl i)) = 0 := by
  rw [adaptedBasis, Basis.map_apply, quotient_sumEquiv, Basis.prod_apply_inl_snd]

theorem adaptedBasis_quotient_right (a : Basis ι K U) (b : Basis τ K (V ⧸ U)) (j : τ) :
    U.mkQ (adaptedBasis h a b (Sum.inr j)) = b j := by
  rw [adaptedBasis, Basis.map_apply, quotient_sumEquiv, Basis.prod_apply_inr_snd]

theorem adaptedBasis_repr_right (a : Basis ι K U) (b : Basis τ K (V ⧸ U)) (x : V) (j : τ) :
    (adaptedBasis h a b).repr x (Sum.inr j) = b.repr (U.mkQ x) j := by
  obtain ⟨y, rfl⟩ := (sumEquiv h).surjective x
  rw [adaptedBasis, quotient_sumEquiv]
  change (a.prod b).repr ((sumEquiv h).symm (sumEquiv h y)) (Sum.inr j) =
    b.repr y.2 j
  rw [LinearEquiv.symm_apply_apply, Basis.prod_repr_inr]

variable [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

variable (T : Module.End K V) (hT : ∀ x ∈ U, T x ∈ U)

def quotientMap : Module.End K (V ⧸ U) :=
  U.mapQ U T (fun x hx => hT x hx)

theorem quotientMap_mkQ (x : V) : quotientMap T hT (U.mkQ x) = U.mkQ (T x) := rfl

include hT in
theorem adapted_lower_left (a : Basis ι K U) (b : Basis τ K (V ⧸ U)) (i : ι) (j : τ) :
    LinearMap.toMatrix (adaptedBasis h a b) (adaptedBasis h a b) T (Sum.inr j) (Sum.inl i) = 0 := by
  rw [LinearMap.toMatrix_apply, adaptedBasis_repr_right,
    ← quotientMap_mkQ T hT, adaptedBasis_quotient_left, map_zero, map_zero] <;> rfl

theorem adapted_lower_right (a : Basis ι K U) (b : Basis τ K (V ⧸ U)) (i j : τ) :
    LinearMap.toMatrix (adaptedBasis h a b) (adaptedBasis h a b) T (Sum.inr i) (Sum.inr j) =
      LinearMap.toMatrix b b (quotientMap T hT) i j := by
  simp only [LinearMap.toMatrix_apply, adaptedBasis_repr_right]
  rw [← quotientMap_mkQ T hT, adaptedBasis_quotient_right]

end
end ManuscriptAudit.InvariantSubspaceMatrixBlocks

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.InvariantSubspaceMatrixBlocks.adaptedBasis_quotient_left,
      ``ManuscriptAudit.InvariantSubspaceMatrixBlocks.adaptedBasis_quotient_right,
      ``ManuscriptAudit.InvariantSubspaceMatrixBlocks.adaptedBasis_repr_right,
      ``ManuscriptAudit.InvariantSubspaceMatrixBlocks.adapted_lower_left,
      ``ManuscriptAudit.InvariantSubspaceMatrixBlocks.adapted_lower_right] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
