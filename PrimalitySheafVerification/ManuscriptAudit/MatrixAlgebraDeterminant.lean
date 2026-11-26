import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Determinant invariance for an automorphism of a full matrix algebra

Images of the matrix units produce a basis-change matrix. Its columns
are obtained from a nonzero vector in one diagonal idempotent's image.
Intertwining with every matrix unit gives determinant invariance.
-/

namespace ManuscriptAudit.MatrixAlgebraDeterminant

open Matrix

noncomputable section

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1500000 in
/-- Every algebra automorphism of a full matrix algebra preserves determinant. -/
theorem det_map (α : Matrix I I K ≃ₐ[K] Matrix I I K) (M : Matrix I I K) :
    (α M).det = M.det := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · letI : IsEmpty I := hI
    simp only [Matrix.det_isEmpty]
  let i₀ := Classical.choice hI
  let e (i j : I) := Matrix.single i j (1 : K)
  have hne : α (e i₀ i₀) ≠ 0 := by
    intro h
    have he : e i₀ i₀ = 0 := α.injective (h.trans α.map_zero.symm)
    have he' := congrArg (fun N : Matrix I I K ↦ N i₀ i₀) he
    simpa [e] using he'
  have hC : ∃ j, (α (e i₀ i₀)).col j ≠ 0 := by
    by_contra! h
    apply hne
    ext i j
    exact congrFun (h j) i
  obtain ⟨j₀, hj₀⟩ := hC
  let v := (α (e i₀ i₀)).mulVec (Pi.single j₀ 1)
  have hv : v ≠ 0 := by simpa [v, Matrix.mulVec_single_one] using hj₀
  let w (i : I) := (α (e i i₀)).mulVec v
  have hw : w i₀ = v := by
    change (α (e i₀ i₀)).mulVec ((α (e i₀ i₀)).mulVec (Pi.single j₀ 1)) = _
    rw [Matrix.mulVec_mulVec, ← map_mul]
    simp [e, v]
  have hAct (i j l : I) :
      (α (e i j)).mulVec (w l) = if j = l then w i else 0 := by
    change (α (e i j)).mulVec ((α (e l i₀)).mulVec v) = _
    rw [Matrix.mulVec_mulVec, ← map_mul]
    by_cases hh : j = l
    · subst l
      simp [e, w]
    · rw [if_neg hh, show e i j * e l i₀ = 0 from
        Matrix.single_mul_single_of_ne (c := (1 : K)) i j l hh (1 : K), map_zero, Matrix.zero_mulVec]
  let P := Matrix.of (fun i j ↦ w j i)
  have hUnit (i j : I) : α (e i j) * P = P * e i j := by
    ext a b
    change (α (e i j)).mulVec (w b) a = (P * e i j) a b
    rw [hAct]
    by_cases hh : j = b
    · subst b
      rw [if_pos rfl]
      simp only [e, Matrix.mul_single_apply_same, mul_one] <;> rfl
    · rw [if_neg hh]
      change 0 = (P * Matrix.single i j (1 : K)) a b
      exact (Matrix.mul_single_apply_of_ne (c := (1 : K)) i j a b (fun h ↦ hh h.symm) P).symm
  have hKernel (z : I → K) (hz : P.mulVec z = 0) : z = 0 := by
    funext j
    have h : P.mulVec ((e i₀ j).mulVec z) = 0 := by
      rw [Matrix.mulVec_mulVec, ← hUnit i₀ j, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    have he : (e i₀ j).mulVec z = z j • Pi.single i₀ (1 : K) := by
      simpa only [e, one_mul] using Matrix.single_mulVec_eq i₀ j (1 : K) z
    rw [he, Matrix.mulVec_smul, Matrix.mulVec_single_one] at h
    change z j • w i₀ = 0 at h
    rw [hw] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have hP : Function.Injective P.mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hKernel
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hDet : P.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det P).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hP))
  have hConj : α M * P = P * M := by
    refine Matrix.induction_on' M (by simp) ?_ ?_
    · intro B C hB hC
      simp only [map_add, add_mul, mul_add, hB, hC]
    · intro i j c
      rw [← show c • e i j = Matrix.single i j c from by simp [e, Matrix.smul_single, smul_eq_mul],
        map_smul, Matrix.smul_mul, Matrix.mul_smul, hUnit]
  have h := congrArg Matrix.det hConj
  rw [Matrix.det_mul, Matrix.det_mul] at h
  exact mul_right_cancel₀ hDet (h.trans (mul_comm P.det M.det))

end

end ManuscriptAudit.MatrixAlgebraDeterminant

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MatrixAlgebraDeterminant.det_map
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
