import Lean.Util.CollectAxioms
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-!
# The ordinary pairing on the compact real gauge directions

The adjoint action of a skew-Hermitian matrix is skew for the actual
Hilbert–Schmidt pairing. The ordinary commutator and this pairing are
both covariant for unitary conjugation.
-/

namespace ManuscriptAudit.Paper10UnitaryGaugePairing

open scoped Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat := Matrix n n ℂ

def pair (Y Z : Mat (n := n)) : ℂ := Matrix.trace (Yᴴ * Z)

def bracket (X Y : Mat (n := n)) : Mat (n := n) := X * Y - Y * X

theorem trace_pair_self (Y : Mat (n := n)) :
    (pair Y Y).re = ∑ i, ∑ j, Complex.normSq (Y j i) := by
  change Complex.reAddGroupHom (∑ i, (Yᴴ * Y) i i) = _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (star (Y j i) * Y j i).re = _
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem trace_pair_nonnegative (Y : Mat (n := n)) : 0 ≤ (pair Y Y).re := by
  rw [trace_pair_self]
  exact Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

theorem pair_hermitian (Y Z : Mat (n := n)) : star (pair Y Z) = pair Z Y := by
  unfold pair
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem adjoint_action_skew (X Y Z : Mat (n := n)) (hX : Xᴴ = -X) :
    pair (bracket X Y) Z = -pair Y (bracket X Z) := by
  have hAdj : (bracket X Y)ᴴ = X * Yᴴ - Yᴴ * X := by
    unfold bracket
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hX]
    noncomm_ring
  have hCyc : Matrix.trace ((X * Yᴴ) * Z) = Matrix.trace (Yᴴ * (Z * X)) := by
    rw [mul_assoc X Yᴴ Z, Matrix.trace_mul_comm X (Yᴴ * Z), mul_assoc]
  unfold pair
  rw [hAdj, sub_mul, Matrix.trace_sub, hCyc]
  unfold bracket
  rw [mul_sub, Matrix.trace_sub, mul_assoc Yᴴ X Z, neg_sub]

theorem projected_adjoint_action_skew (P : Mat (n := n) → Mat (n := n))
    (hP : ∀ Y Z, pair (P Y) Z = pair Y (P Z))
    (X Y Z : Mat (n := n)) (hX : Xᴴ = -X) (hY : P Y = Y) (hZ : P Z = Z) :
    pair (P (bracket X Y)) Z = -pair Y (P (bracket X Z)) := by
  calc
    _ = pair (bracket X Y) Z := by rw [hP, hZ]
    _ = -pair Y (bracket X Z) := adjoint_action_skew X Y Z hX
    _ = _ := by rw [← hP, hY]

theorem real_diagonal_vanishes (X Y : Mat (n := n)) (hX : Xᴴ = -X) :
    (pair (bracket X Y) Y).re = 0 := by
  have h := adjoint_action_skew X Y Y hX
  rw [← pair_hermitian (bracket X Y) Y] at h
  have hRe := congrArg Complex.re h
  change (pair (bracket X Y) Y).re = (-(star (pair (bracket X Y) Y))).re at hRe
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at hRe
  linarith

def conjugate (U Y : Mat (n := n)) : Mat (n := n) := U * Y * Uᴴ

theorem conjugation_preserves_pair (U Y Z : Mat (n := n)) (hU : Uᴴ * U = 1) :
    pair (conjugate U Y) (conjugate U Z) = pair Y Z := by
  have hReduce (W : Mat (n := n)) : Uᴴ * (U * W) = W := by
    rw [← mul_assoc, hU, one_mul]
  have hStar : (conjugate U Y)ᴴ = conjugate U Yᴴ := by
    simp only [conjugate, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
  unfold pair
  rw [hStar]
  calc
    _ = Matrix.trace (U * (Yᴴ * Z) * Uᴴ) := by
      simp only [conjugate, mul_assoc, hReduce]
    _ = _ := by rw [Matrix.trace_mul_comm (U * (Yᴴ * Z)) Uᴴ, ← mul_assoc, hU, one_mul]

theorem commutator_covariant (U X Y : Mat (n := n)) (hU : Uᴴ * U = 1) :
    bracket (conjugate U X) (conjugate U Y) = conjugate U (bracket X Y) := by
  have hReduce (W : Mat (n := n)) : Uᴴ * (U * W) = W := by
    rw [← mul_assoc, hU, one_mul]
  have hMul (A B : Mat (n := n)) : conjugate U A * conjugate U B = conjugate U (A * B) := by
    simp only [conjugate, mul_assoc, hReduce]
  unfold bracket
  rw [hMul, hMul]
  simp only [conjugate, mul_sub, sub_mul]

end ManuscriptAudit.Paper10UnitaryGaugePairing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.trace_pair_self,
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.trace_pair_nonnegative,
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.pair_hermitian,
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.adjoint_action_skew,
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.projected_adjoint_action_skew,
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.real_diagonal_vanishes,
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.conjugation_preserves_pair,
      ``ManuscriptAudit.Paper10UnitaryGaugePairing.commutator_covariant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
