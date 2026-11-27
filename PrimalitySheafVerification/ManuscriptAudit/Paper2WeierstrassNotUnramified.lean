import Lean.Util.CollectAxioms
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Unramified.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassDualLifts

/-! A smooth affine Weierstrass point disproves formal unramifiedness of the whole curve over its field. -/

namespace ManuscriptAudit.Paper2WeierstrassNotUnramified

open WeierstrassCurve Polynomial Paper2WeierstrassDualLifts
open scoped DualNumber

noncomputable section

variable {K : Type*} [Field K]

private def evaluation {R : Type*} [CommRing R] [Algebra K R] (W : WeierstrassCurve K)
    (x y : R) (h : (W.map (algebraMap K R)).toAffine.Equation x y) :
    W.toAffine.CoordinateRing →ₐ[K] R := by
  let b : Polynomial K →ₐ[K] R := Polynomial.aeval x
  have hr : W.toAffine.polynomial.eval₂ b.toRingHom y = 0 := by
    have hEq := (Affine.equation_iff' (W := (W.map (algebraMap K R)).toAffine) x y).mp h
    simpa only [Affine.polynomial, b, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C, AlgHom.coe_toRingHom, map_add, map_mul, map_pow, aeval_X, aeval_C,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using hEq
  exact AdjoinRoot.liftAlgHom W.toAffine.polynomial b y hr

private theorem evaluation_x {R : Type*} [CommRing R] [Algebra K R] (W : WeierstrassCurve K)
    (x y : R) (h : (W.map (algebraMap K R)).toAffine.Equation x y) :
    evaluation W x y h (AdjoinRoot.of W.toAffine.polynomial X) = x := by
  unfold evaluation
  rw [AdjoinRoot.liftAlgHom_of, aeval_X]

private theorem evaluation_y {R : Type*} [CommRing R] [Algebra K R] (W : WeierstrassCurve K)
    (x y : R) (h : (W.map (algebraMap K R)).toAffine.Equation x y) :
    evaluation W x y h (AdjoinRoot.root W.toAffine.polynomial) = y := by
  unfold evaluation
  rw [AdjoinRoot.liftAlgHom_root]

theorem not_formally_unramified (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) : ¬ Algebra.FormallyUnramified K W.toAffine.CoordinateRing := by
  intro hUnramified
  letI : Algebra.FormallyUnramified K W.toAffine.CoordinateRing := hUnramified
  apply nonunique_dual_lift W x y h
  constructor
  intro a b
  let g (z : DualLifts W x y) : W.toAffine.CoordinateRing →ₐ[K] K[ε] :=
    evaluation W ⟨x, z.1.1⟩ ⟨y, z.1.2⟩ z.2
  let r : K[ε] →ₐ[K] K := TrivSqZeroExt.fstHom K K K
  have hSame : r.comp (g a) = r.comp (g b) := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change r (g a (AdjoinRoot.of W.toAffine.polynomial X)) =
        r (g b (AdjoinRoot.of W.toAffine.polynomial X))
      simp only [g, evaluation_x, r, TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_mk]
    · change r (g a (AdjoinRoot.root W.toAffine.polynomial)) =
        r (g b (AdjoinRoot.root W.toAffine.polynomial))
      simp only [g, evaluation_y, r, TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_mk]
  have hNil : IsNilpotent (RingHom.ker (r : K[ε] →+* K)) := by
    refine ⟨2, ?_⟩
    exact TrivSqZeroExt.kerIdeal_sq K K
  have he := Algebra.FormallyUnramified.lift_unique' r hNil (g a) (g b) hSame
  apply Subtype.ext
  apply Prod.ext
  · have hx := congrArg (fun f : W.toAffine.CoordinateRing →ₐ[K] K[ε] =>
        (f (AdjoinRoot.of W.toAffine.polynomial X)).snd) he
    simpa only [g, evaluation_x, TrivSqZeroExt.snd_mk] using hx
  · have hy := congrArg (fun f : W.toAffine.CoordinateRing →ₐ[K] K[ε] =>
        (f (AdjoinRoot.root W.toAffine.polynomial)).snd) he
    simpa only [g, evaluation_y, TrivSqZeroExt.snd_mk] using hy

end
end ManuscriptAudit.Paper2WeierstrassNotUnramified

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper2WeierstrassNotUnramified.not_formally_unramified
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
