import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Norm.Basic

/-!
# The norm of a homogeneous polynomial

The coefficientwise matrix of left multiplication gives a polynomial
over the base field. Its determinant evaluates to the actual field
norm and multiplies the homogeneous degree by the extension degree.
-/

namespace ManuscriptAudit.HomogeneousPolynomialNorm

open MvPolynomial

noncomputable section

variable {F E σ : Type*} [Field F] [Field E] [Algebra F E]

private def applyCoefficients (f : E →ₗ[F] F) (P : MvPolynomial σ E) : MvPolynomial σ F :=
  ∑ m ∈ P.support, monomial m (f (P.coeff m))

private theorem applyCoefficients_homogeneous (f : E →ₗ[F] F) {P : MvPolynomial σ E}
    {d : ℕ} (hP : P.IsHomogeneous d) : (applyCoefficients f P).IsHomogeneous d := by
  unfold applyCoefficients
  apply IsHomogeneous.sum
  intro m hm
  apply isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  exact hP (mem_support_iff.mp hm)

private theorem eval_applyCoefficients (f : E →ₗ[F] F) (P : MvPolynomial σ E) (z : σ → F) :
    eval z (applyCoefficients f P) =
      f (P.eval₂ (RingHom.id E) (fun i ↦ algebraMap F E (z i))) := by
  classical
  unfold applyCoefficients
  rw [map_sum, eval₂_eq, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial, RingHom.id_apply]
  let t := m.prod (fun i n ↦ z i ^ n)
  have ht : (∏ i ∈ m.support, algebraMap F E (z i) ^ m i) = algebraMap F E t := by
    simp only [t, Finsupp.prod, map_prod, map_pow]
  rw [ht]
  change f (P.coeff m) * t = f (P.coeff m * algebraMap F E t)
  rw [mul_comm (P.coeff m), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

variable {n : ℕ} (b : Module.Basis (Fin n) F E)

private def coordinate (i j : Fin n) : E →ₗ[F] F where
  toFun x := Algebra.leftMulMatrix b x i j
  map_add' x y := by simp
  map_smul' r x := by simp [Matrix.smul_apply]

private def matrix (P : MvPolynomial σ E) : Matrix (Fin n) (Fin n) (MvPolynomial σ F) :=
  fun i j ↦ applyCoefficients (coordinate b i j) P

/-- The determinant norm polynomial over the base field. -/
def normPolynomial (P : MvPolynomial σ E) : MvPolynomial σ F :=
  (matrix b P).det

/-- The norm of a homogeneous polynomial has the expected degree. -/
theorem normPolynomial_homogeneous {P : MvPolynomial σ E} {d : ℕ}
    (hP : P.IsHomogeneous d) : (normPolynomial b P).IsHomogeneous (n * d) := by
  classical
  unfold normPolynomial
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro τ _
  have hp := IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i ↦ matrix b P (τ i) i) (fun _ ↦ d) (by
      intro i _
      exact applyCoefficients_homogeneous (coordinate b (τ i) i) hP)
  have hProd : (∏ i : Fin n, matrix b P (τ i) i).IsHomogeneous (n * d) := by
    simpa [Nat.mul_comm] using hp
  change (((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ F) *
    ∏ i : Fin n, matrix b P (τ i) i).IsHomogeneous (n * d)
  rw [← map_intCast (C : F →+* MvPolynomial σ F)]
  exact hProd.C_mul _

/-- Evaluation of the determinant polynomial is the actual field norm. -/
theorem eval_normPolynomial (P : MvPolynomial σ E) (z : σ → F) :
    eval z (normPolynomial b P) =
      Algebra.norm F (P.eval₂ (RingHom.id E) (fun i ↦ algebraMap F E (z i))) := by
  let x := P.eval₂ (RingHom.id E) (fun i ↦ algebraMap F E (z i))
  change eval z (matrix b P).det = Algebra.norm F x
  have h : (eval z).mapMatrix (matrix b P) = Algebra.leftMulMatrix b x := by
    ext i j
    exact eval_applyCoefficients (coordinate b i j) P z
  rw [RingHom.map_det, h, Algebra.norm_eq_matrix_det b x]

end

end ManuscriptAudit.HomogeneousPolynomialNorm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.HomogeneousPolynomialNorm.normPolynomial_homogeneous,
      ``ManuscriptAudit.HomogeneousPolynomialNorm.eval_normPolynomial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
