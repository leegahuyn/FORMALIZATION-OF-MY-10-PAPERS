import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Data.Fin.SuccPred
import Mathlib.RingTheory.Norm.Basic
import PrimalitySheafVerification.ManuscriptAudit.RatFuncTsen

/-!
# Surjectivity of field norms over K(t)

The determinant of the generic left multiplication matrix is a
homogeneous norm form. Applying Tsen's theorem to that form minus
a scalar multiple of one more variable to the degree proves
surjectivity of the actual field norm.
-/

namespace ManuscriptAudit.RatFuncTsen

open MvPolynomial
open scoped BigOperators

noncomputable section

private def normMatrix {F E : Type*} [Field F] [Field E] [Algebra F E] {n : ℕ}
    (b : Module.Basis (Fin n) F E) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n + 1)) F) :=
  fun i j => ∑ k : Fin n,
    C (Algebra.leftMulMatrix b (b k) i j) * X k.castSucc

private theorem normMatrix_det_homogeneous {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} (b : Module.Basis (Fin n) F E) :
    (normMatrix b).det.IsHomogeneous n := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro σ _
  have hp := IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => normMatrix b (σ i) i) (fun _ => 1) (by
      intro i _
      change (∑ k : Fin n, C (Algebra.leftMulMatrix b (b k) (σ i) i) *
        X k.castSucc).IsHomogeneous 1
      apply IsHomogeneous.sum
      intro k _
      exact isHomogeneous_C_mul_X _ _)
  have hp' : (∏ i : Fin n, normMatrix b (σ i) i).IsHomogeneous n := by
    simpa using hp
  change (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin (n + 1)) F) *
    ∏ i : Fin n, normMatrix b (σ i) i).IsHomogeneous n
  rw [← map_intCast (C : F →+* MvPolynomial (Fin (n + 1)) F)]
  exact hp'.C_mul _

private theorem eval_normMatrix_det {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} (b : Module.Basis (Fin n) F E) (z : Fin (n + 1) → F) :
    aeval z (normMatrix b).det =
      Algebra.norm F (b.equivFun.symm (fun i => z i.castSucc)) := by
  let x := b.equivFun.symm (fun i => z i.castSucc)
  have hX : x = ∑ k : Fin n, z k.castSucc • b k := b.equivFun_symm_apply _
  have hMatrix : (aeval z).mapMatrix (normMatrix b) = Algebra.leftMulMatrix b x := by
    ext i j
    change aeval z (∑ k : Fin n, C (Algebra.leftMulMatrix b (b k) i j) *
      X k.castSucc) = Algebra.leftMulMatrix b x i j
    rw [hX]
    simp [map_sum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]
  change aeval z (normMatrix b).det = Algebra.norm F x
  rw [AlgHom.map_det, hMatrix, Algebra.norm_eq_matrix_det b x]

/-- Every scalar is a field norm from a finite extension of a field
with the homogeneous zero property C1. -/
theorem norm_surjective_of_C1 (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (hC : ∀ {m d : ℕ} (P : MvPolynomial (Fin m) F), P.IsHomogeneous d →
      0 < d → d < m → ∃ z : Fin m → F, z ≠ 0 ∧ aeval z P = 0) :
    Function.Surjective (fun x : E => Algebra.norm F x) := by
  let n := Module.finrank F E
  let b : Module.Basis (Fin n) F E := Module.finBasis F E
  have hn : 0 < n := Module.finrank_pos
  intro a
  let P := (normMatrix b).det - C a * X (Fin.last n) ^ n
  have hP : P.IsHomogeneous n :=
    (normMatrix_det_homogeneous b).sub (isHomogeneous_C_mul_X_pow _ _ _)
  obtain ⟨z, hz, heval⟩ := hC P hP hn (Nat.lt_succ_self n)
  let x := b.equivFun.symm (fun i => z i.castSucc)
  let t := z (Fin.last n)
  have hNorm : Algebra.norm F x = a * t ^ n := by
    change aeval z ((normMatrix b).det - C a * X (Fin.last n) ^ n) = 0 at heval
    rw [map_sub, map_mul, map_pow, aeval_C, aeval_X, eval_normMatrix_det] at heval
    exact sub_eq_zero.mp heval
  have ht : t ≠ 0 := by
    intro h
    have hzero : Algebra.norm F x = 0 := by
      rw [hNorm, h, zero_pow (Nat.ne_of_gt hn), mul_zero]
    have hx : x = 0 := Algebra.norm_eq_zero_iff.mp hzero
    have hcoords : (fun i : Fin n => z i.castSucc) = 0 := by
      simpa only [x, LinearEquiv.apply_symm_apply, map_zero] using congrArg b.equivFun hx
    apply hz
    funext i
    exact Fin.lastCases h (fun j => congrFun hcoords j) i
  refine ⟨x * (algebraMap F E t)⁻¹, ?_⟩
  change Algebra.norm F (x * (algebraMap F E t)⁻¹) = a
  rw [map_mul, Algebra.norm_inv, Algebra.norm_algebraMap, hNorm]
  change (a * t ^ n) * (t ^ n)⁻¹ = a
  rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero n ht), mul_one]

/-- Every scalar is a field norm from a finite extension of the
rational function field of an algebraically closed field. -/
theorem norm_surjective (K E : Type*) [Field K] [IsAlgClosed K] [Field E]
    [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E] :
    Function.Surjective (fun x : E => Algebra.norm (RatFunc K) x) :=
  norm_surjective_of_C1 (RatFunc K) E (fun P hP hd hm ↦ exists_ratFunc_zero P hP hd hm)

/-- The norm is surjective on the actual unit groups as well. -/
theorem norm_units_surjective (K E : Type*) [Field K] [IsAlgClosed K] [Field E]
    [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E] :
    Function.Surjective (Units.map (Algebra.norm (RatFunc K) : E →* RatFunc K)) := by
  intro u
  obtain ⟨x, hx⟩ := norm_surjective K E (u : RatFunc K)
  have hx' : x ≠ 0 := by
    rintro rfl
    change Algebra.norm (RatFunc K) (0 : E) = (u : RatFunc K) at hx
    rw [Algebra.norm_zero] at hx
    exact u.ne_zero hx.symm
  exact ⟨Units.mk0 x hx', Units.ext hx⟩

end

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncTsen.norm_surjective_of_C1,
      ``ManuscriptAudit.RatFuncTsen.norm_surjective,
      ``ManuscriptAudit.RatFuncTsen.norm_units_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
