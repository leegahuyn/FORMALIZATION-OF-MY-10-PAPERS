import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant

/-! An injective intertwiner between equal-rank finite free modules over
a domain preserves the integral characteristic polynomial. -/

namespace ManuscriptAudit.CharpolyInjectiveIntertwiner

open Module Polynomial

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matrix_charpoly (A B C₀ : Matrix ι ι R)
    (h : C₀ * A = B * C₀) (hd : C₀.det ≠ 0) :
    A.charpoly = B.charpoly := by
  let e : R →+* R[X] := Polynomial.C
  let c := e.mapMatrix C₀
  have hs : c * Matrix.scalar ι (X : R[X]) = Matrix.scalar ι (X : R[X]) * c := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  have hm : c * e.mapMatrix A = e.mapMatrix B * c := by
    change e.mapMatrix C₀ * e.mapMatrix A = e.mapMatrix B * e.mapMatrix C₀
    rw [← map_mul, ← map_mul, h]
  have hc : c * A.charmatrix = B.charmatrix * c := by
    change c * (Matrix.scalar ι (X : R[X]) - e.mapMatrix A) =
      (Matrix.scalar ι (X : R[X]) - e.mapMatrix B) * c
    rw [mul_sub, sub_mul, hs, hm]
  have hp := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_mul] at hp
  change c.det * A.charpoly = B.charpoly * c.det at hp
  have hn : c.det ≠ 0 := by
    change Matrix.det (e.mapMatrix C₀) ≠ 0
    rw [← RingHom.map_det]
    intro hzero
    apply hd
    apply Polynomial.C_injective
    exact hzero.trans (map_zero e).symm
  exact mul_left_cancel₀ hn (hp.trans (mul_comm _ _))

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]

/-- Integral characteristic polynomials coincide under an injective
linear comparison if both modules have the same finite basis index. -/
theorem charpoly_eq (bM : Basis ι R M) (bN : Basis ι R N)
    (A : Module.End R M) (B : Module.End R N) (f : M →ₗ[R] N)
    (hf : Function.Injective f) (h : f.comp A = B.comp f) :
    A.charpoly = B.charpoly := by
  let e : N ≃ₗ[R] M := bN.equivFun.trans bM.equivFun.symm
  let g : Module.End R M := e.toLinearMap.comp f
  have hg : Function.Injective g := e.injective.comp hf
  have hdet : LinearMap.det g ≠ 0 := by
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hg)
  have h' : g.comp A = (e.conj B).comp g := by
    ext x
    change e (f (A x)) = e (B (e.symm (e (f x))))
    rw [e.symm_apply_apply]
    exact congrArg e (DFunLike.congr_fun h x)
  have hm := congrArg (LinearMap.toMatrix bM bM) h'
  rw [LinearMap.toMatrix_comp bM bM bM, LinearMap.toMatrix_comp bM bM bM] at hm
  have hmat := matrix_charpoly
    (LinearMap.toMatrix bM bM A) (LinearMap.toMatrix bM bM (e.conj B))
    (LinearMap.toMatrix bM bM g) hm
    (by rwa [LinearMap.det_toMatrix])
  calc
    A.charpoly = (LinearMap.toMatrix bM bM A).charpoly := (LinearMap.charpoly_toMatrix A bM).symm
    _ = (LinearMap.toMatrix bM bM (e.conj B)).charpoly := hmat
    _ = (e.conj B).charpoly := LinearMap.charpoly_toMatrix (e.conj B) bM
    _ = B.charpoly := LinearEquiv.charpoly_conj e B

end

end ManuscriptAudit.CharpolyInjectiveIntertwiner

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CharpolyInjectiveIntertwiner.charpoly_eq
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
