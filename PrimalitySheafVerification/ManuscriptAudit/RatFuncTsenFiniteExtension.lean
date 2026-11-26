import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HomogeneousPolynomialNorm
import PrimalitySheafVerification.ManuscriptAudit.RatFuncTsen

/-!
# Tsen's property for finite extensions of K(t)

Express each variable in a basis over K(t) and take the genuine norm
polynomial. The degree and number of variables are both multiplied
by the extension degree. Tsen's theorem then gives a nonzero zero
of the original homogeneous polynomial.
-/

namespace ManuscriptAudit.RatFuncTsen

open MvPolynomial HomogeneousPolynomialNorm

noncomputable section

variable {L F : Type*} [Field L] [Field F] [Algebra F L]

private def basisForm {m n : ℕ} (b : Module.Basis (Fin m) F L) (i : Fin n) :
    MvPolynomial (Fin (n * m)) L :=
  ∑ j : Fin m, C (b j) * X (finProdFinEquiv (i, j))

private theorem basisForm_homogeneous {m n : ℕ} (b : Module.Basis (Fin m) F L) (i : Fin n) :
    (basisForm b i).IsHomogeneous 1 := by
  unfold basisForm
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X _ _

private theorem aeval_basisForm_homogeneous {m n d : ℕ} (b : Module.Basis (Fin m) F L)
    {P : MvPolynomial (Fin n) L} (hP : P.IsHomogeneous d) :
    (aeval (basisForm b) P).IsHomogeneous d := by
  classical
  rw [aeval_def, eval₂_eq]
  apply IsHomogeneous.sum
  intro v hv
  have hV : v.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.mp hv)
  have h := IsHomogeneous.prod v.support
    (fun i ↦ basisForm b i ^ v i) (fun i ↦ v i) (by
      intro i _
      simpa only [one_mul] using (basisForm_homogeneous b i).pow (v i))
  rw [← Finsupp.degree_apply, hV] at h
  exact h.C_mul _

private theorem aeval_basisForm {m n : ℕ} (b : Module.Basis (Fin m) F L)
    (z : Fin (n * m) → F) (i : Fin n) :
    aeval (fun j ↦ algebraMap F L (z j)) (basisForm b i) =
      b.equivFun.symm (fun j ↦ z (finProdFinEquiv (i, j))) := by
  rw [basisForm, b.equivFun_symm_apply]
  simp [map_sum, Algebra.smul_def, mul_comm]

set_option maxHeartbeats 1500000 in
/-- Every finite extension of the rational function field over an
algebraically closed field has the homogeneous equation property C1. -/
theorem exists_finiteExtension_zero (K L : Type*) [Field K] [IsAlgClosed K] [Field L]
    [Algebra (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
    {n d : ℕ} (P : MvPolynomial (Fin n) L) (hP : P.IsHomogeneous d)
    (hd : 0 < d) (hn : d < n) :
    ∃ x : Fin n → L, x ≠ 0 ∧ aeval x P = 0 := by
  let F := RatFunc K
  let m := Module.finrank F L
  let b : Module.Basis (Fin m) F L := Module.finBasis F L
  let Q := aeval (basisForm b) P
  let N := normPolynomial b Q
  have hm : 0 < m := Module.finrank_pos
  have hQ : Q.IsHomogeneous d := aeval_basisForm_homogeneous b hP
  have hN : N.IsHomogeneous (m * d) := normPolynomial_homogeneous b hQ
  have hD : m * d < n * m := by
    rw [Nat.mul_comm m d]
    exact Nat.mul_lt_mul_of_pos_right hn hm
  obtain ⟨z, hz, hZ⟩ := exists_ratFunc_zero N hN (Nat.mul_pos hm hd) hD
  let v (j : Fin (n * m)) : L := algebraMap F L (z j)
  let x (i : Fin n) : L := b.equivFun.symm (fun j ↦ z (finProdFinEquiv (i, j)))
  have hx : x ≠ 0 := by
    intro h
    apply hz
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    have hRow : (fun l : Fin m ↦ z (finProdFinEquiv (i, l))) = 0 := by
      apply b.equivFun.symm.injective
      rw [map_zero]
      exact congrFun h i
    exact congrFun hRow j
  have hNorm : Algebra.norm F (aeval v Q) = 0 := by
    change eval z (normPolynomial b Q) = 0 at hZ
    rw [eval_normPolynomial] at hZ
    exact hZ
  have hEval : aeval v Q = 0 := Algebra.norm_eq_zero_iff.mp hNorm
  have hComp : aeval v Q = aeval x P := by
    change aeval v (aeval (basisForm b) P) = _
    rw [comp_aeval_apply]
    congr 1
    funext i
    exact aeval_basisForm b z i
  exact ⟨x, hx, hComp.symm.trans hEval⟩

end

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RatFuncTsen.exists_finiteExtension_zero
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
