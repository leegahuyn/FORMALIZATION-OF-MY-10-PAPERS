import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar twists of a split division algebra

A splitting over a field extension gives a matrix representation of the
division algebra. Applying an automorphism of the extension to the
matrix entries is realized on its image by an algebra automorphism over
the extension. This is obtained by canceling the scalar twist on the
tensor-product side.
-/

namespace ManuscriptAudit.DivisionAlgebraSplitTwist

open scoped TensorProduct

noncomputable section

variable {F L D : Type*} [Field F] [Field L] [Algebra F L]
  [DivisionRing D] [Algebra F D] {n : ℕ}

private abbrev M := Matrix (Fin n) (Fin n) L

/-- The base-algebra matrix representation supplied by an actual splitting. -/
def representation (s : L ⊗[F] D ≃ₐ[L] M (L := L) (n := n)) :
    D →ₐ[F] M (L := L) (n := n) :=
  (s.restrictScalars F).toAlgHom.comp Algebra.TensorProduct.includeRight

private def twistTensor (τ : L ≃ₐ[F] L) : L ⊗[F] D ≃ₐ[F] L ⊗[F] D :=
  Algebra.TensorProduct.congr τ.symm (AlgEquiv.refl : D ≃ₐ[F] D)

private def twistMatrices (τ : L ≃ₐ[F] L) :
    M (L := L) (n := n) ≃ₐ[F] M (L := L) (n := n) :=
  τ.mapMatrix

private theorem twistMatrices_algebraMap (τ : L ≃ₐ[F] L) (a : L) :
    twistMatrices (n := n) τ (algebraMap L (M (L := L) (n := n)) a) =
      algebraMap L (M (L := L) (n := n)) (τ a) := by
  ext i j
  change τ ((algebraMap L (M (L := L) (n := n)) a) i j) =
    (algebraMap L (M (L := L) (n := n)) (τ a)) i j
  rw [Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

/-- The semilinear twist induces a genuine automorphism over the splitting field. -/
def splitTwist (s : L ⊗[F] D ≃ₐ[L] M (L := L) (n := n)) (τ : L ≃ₐ[F] L) :
    M (L := L) (n := n) ≃ₐ[L] M (L := L) (n := n) := by
  let e := s.toRingEquiv.symm.trans (twistTensor (D := D) τ).toRingEquiv |>.trans s.toRingEquiv
    |>.trans (twistMatrices (n := n) τ).toRingEquiv
  refine { e with commutes' := fun a ↦ ?_ }
  change twistMatrices τ (s (twistTensor τ (s.symm (algebraMap L _ a)))) =
    algebraMap L _ a
  rw [s.symm.commutes]
  have hT : twistTensor (D := D) τ (algebraMap L (L ⊗[F] D) a) =
      algebraMap L (L ⊗[F] D) (τ.symm a) := by
    change twistTensor τ (a ⊗ₜ[F] (1 : D)) = τ.symm a ⊗ₜ[F] (1 : D)
    simp [twistTensor]
  rw [hT, s.commutes, twistMatrices_algebraMap, AlgEquiv.apply_symm_apply]

/-- On the represented division algebra, the automorphism applies the
Galois automorphism to every matrix coefficient. -/
theorem splitTwist_representation
    (s : L ⊗[F] D ≃ₐ[L] M (L := L) (n := n)) (τ : L ≃ₐ[F] L) (x : D) :
    splitTwist s τ (representation s x) = τ.toRingHom.mapMatrix (representation s x) := by
  change twistMatrices τ (s (twistTensor τ (s.symm (s (1 ⊗ₜ[F] x))))) = _
  rw [AlgEquiv.symm_apply_apply]
  have h : twistTensor (D := D) τ (1 ⊗ₜ[F] x) = 1 ⊗ₜ[F] x := by
    simp [twistTensor]
  rw [h]
  rfl

end

end ManuscriptAudit.DivisionAlgebraSplitTwist

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DivisionAlgebraSplitTwist.representation,
      ``ManuscriptAudit.DivisionAlgebraSplitTwist.splitTwist_representation] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
