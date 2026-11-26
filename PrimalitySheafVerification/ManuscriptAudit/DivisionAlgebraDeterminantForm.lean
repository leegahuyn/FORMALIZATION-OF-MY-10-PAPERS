import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The determinant form of a division algebra representation

A matrix representation of a division algebra gives a homogeneous
determinant polynomial in basis coordinates. A nonzero vector in
these coordinates represents a unit and has nonzero determinant.
-/

namespace ManuscriptAudit.DivisionAlgebraDeterminantForm

open MvPolynomial

noncomputable section

variable {F L D : Type*} [Field F] [Field L] [Algebra F L]
  [DivisionRing D] [Algebra F D] {m n : ℕ}
variable (b : Module.Basis (Fin m) F D) (r : D →ₐ[F] Matrix (Fin n) (Fin n) L)

private def genericMatrix : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) L) :=
  fun i j ↦ ∑ k : Fin m, C (r (b k) i j) * X k

/-- The determinant of the generic basis combination in the representation. -/
def determinantForm : MvPolynomial (Fin m) L := (genericMatrix b r).det

/-- The determinant form has homogeneous degree equal to the matrix size. -/
theorem determinantForm_homogeneous : (determinantForm b r).IsHomogeneous n := by
  classical
  unfold determinantForm
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro τ _
  have hp := IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i ↦ genericMatrix b r (τ i) i) (fun _ ↦ 1) (by
      intro i _
      unfold genericMatrix
      apply IsHomogeneous.sum
      intro k _
      exact isHomogeneous_C_mul_X _ _)
  have h : (∏ i : Fin n, genericMatrix b r (τ i) i).IsHomogeneous n := by simpa using hp
  rw [← map_intCast (C : L →+* MvPolynomial (Fin m) L)]
  exact h.C_mul _

/-- Evaluation of the form computes the determinant of the represented element. -/
theorem eval_determinantForm (z : Fin m → F) :
    aeval (fun i ↦ algebraMap F L (z i)) (determinantForm b r) =
      (r (b.equivFun.symm z)).det := by
  let f := aeval (fun i ↦ algebraMap F L (z i))
  change f (genericMatrix b r).det = _
  have h : f.mapMatrix (genericMatrix b r) = r (b.equivFun.symm z) := by
    ext i j
    change f (∑ k : Fin m, C (r (b k) i j) * X k) = r (b.equivFun.symm z) i j
    rw [b.equivFun_symm_apply]
    simp [f, map_sum, Matrix.sum_apply, Matrix.smul_apply, Algebra.smul_def, mul_comm]
  rw [AlgHom.map_det, h]

/-- Evaluation after mapping the coefficients is the determinant of the
coefficientwise image of the represented basis combination. -/
theorem eval_map_determinantForm (φ : L →+* L) (z : Fin m → L) :
    eval z (map φ (determinantForm b r)) =
      (∑ i : Fin m, z i • φ.mapMatrix (r (b i))).det := by
  rw [eval_map]
  let f := eval₂Hom φ z
  change f (genericMatrix b r).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change f (∑ k : Fin m, C (r (b k) i j) * X k) =
    (∑ k : Fin m, z k • φ.mapMatrix (r (b k))) i j
  simp [f, Matrix.sum_apply, Matrix.smul_apply, mul_comm]

/-- A coordinate zero of the determinant form is the zero vector. -/
theorem determinantForm_anisotropic (z : Fin m → F)
    (h : aeval (fun i ↦ algebraMap F L (z i)) (determinantForm b r) = 0) : z = 0 := by
  rw [eval_determinantForm] at h
  by_contra hn
  have hx : b.equivFun.symm z ≠ 0 := by
    intro he
    exact hn (b.equivFun.symm.injective (he.trans b.equivFun.symm.map_zero.symm))
  have hi : IsUnit (r (b.equivFun.symm z)) := (isUnit_iff_ne_zero.mpr hx).map r.toMonoidHom
  exact (isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det.mp hi)) h

end

end ManuscriptAudit.DivisionAlgebraDeterminantForm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DivisionAlgebraDeterminantForm.determinantForm_homogeneous,
      ``ManuscriptAudit.DivisionAlgebraDeterminantForm.eval_determinantForm,
      ``ManuscriptAudit.DivisionAlgebraDeterminantForm.eval_map_determinantForm,
      ``ManuscriptAudit.DivisionAlgebraDeterminantForm.determinantForm_anisotropic] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
