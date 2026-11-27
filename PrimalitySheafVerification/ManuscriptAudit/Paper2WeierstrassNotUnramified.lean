import Lean.Util.CollectAxioms
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Unramified.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassDualLifts
import PrimalitySheafVerification.ManuscriptAudit.LocalizedDualLiftObstruction

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

/-- Evaluation on the actual affine coordinate algebra at the residual point. -/
def residueAt (W : WeierstrassCurve K) (x y : K) (h : W.toAffine.Equation x y) :
    W.toAffine.CoordinateRing →ₐ[K] K :=
  evaluation W x y (by simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id] using h)

/-- The actual affine algebra morphism associated to a first-order coordinate lift. -/
def dualEvaluation (W : WeierstrassCurve K) (x y : K) (z : DualLifts W x y) :
    W.toAffine.CoordinateRing →ₐ[K] K[ε] :=
  evaluation W (dual x z.1.1) (dual y z.1.2) z.2

theorem dualEvaluation_residue (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Equation x y) (a : DualLifts W x y) :
    (TrivSqZeroExt.fstHom K K K).comp (dualEvaluation W x y a) = residueAt W x y h := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change (TrivSqZeroExt.fstHom K K K) (dualEvaluation W x y a (AdjoinRoot.of W.toAffine.polynomial X)) =
      residueAt W x y h (AdjoinRoot.of W.toAffine.polynomial X)
    simp only [dualEvaluation, residueAt, evaluation_x, TrivSqZeroExt.fstHom_apply,
      fst_dual]
  · change (TrivSqZeroExt.fstHom K K K) (dualEvaluation W x y a (AdjoinRoot.root W.toAffine.polynomial)) =
      residueAt W x y h (AdjoinRoot.root W.toAffine.polynomial)
    simp only [dualEvaluation, residueAt, evaluation_y, TrivSqZeroExt.fstHom_apply,
      fst_dual]

theorem dualEvaluation_injective (W : WeierstrassCurve K) (x y : K) :
    Function.Injective (dualEvaluation W x y) := by
  intro a b he
  apply Subtype.ext
  apply Prod.ext
  · have hx := congrArg (fun f : W.toAffine.CoordinateRing →ₐ[K] K[ε] =>
        (f (AdjoinRoot.of W.toAffine.polynomial X)).snd) he
    simpa only [dualEvaluation, evaluation_x, snd_dual] using hx
  · have hy := congrArg (fun f : W.toAffine.CoordinateRing →ₐ[K] K[ε] =>
        (f (AdjoinRoot.root W.toAffine.polynomial)).snd) he
    simpa only [dualEvaluation, evaluation_y, snd_dual] using hy

theorem not_formally_unramified (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) : ¬ Algebra.FormallyUnramified K W.toAffine.CoordinateRing := by
  intro hUnramified
  letI : Algebra.FormallyUnramified K W.toAffine.CoordinateRing := hUnramified
  apply nonunique_dual_lift W x y h
  constructor
  intro a b
  let r : K[ε] →ₐ[K] K := TrivSqZeroExt.fstHom K K K
  have hEq : W.toAffine.Equation x y := ((Affine.nonsingular_iff' (W := W.toAffine) x y).mp h).1
  have hSame : r.comp (dualEvaluation W x y a) = r.comp (dualEvaluation W x y b) :=
    (dualEvaluation_residue W x y hEq a).trans (dualEvaluation_residue W x y hEq b).symm
  have hNil : IsNilpotent (RingHom.ker r.toRingHom) := ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩
  exact dualEvaluation_injective W x y
    (Algebra.FormallyUnramified.lift_unique' r hNil (dualEvaluation W x y a)
      (dualEvaluation W x y b) hSame)

/-- Formal unramifiedness also fails on the actual local ring at the nonsingular point. -/
theorem local_not_formally_unramified (W : WeierstrassCurve K) (x y : K)
    (hEq : W.toAffine.Equation x y) (h : W.toAffine.Nonsingular x y)
    (P : Ideal W.toAffine.CoordinateRing) [P.IsPrime]
    (hP : P = RingHom.ker (residueAt W x y hEq).toRingHom)
    (S : Type*) [CommRing S] [Algebra K S] [Algebra W.toAffine.CoordinateRing S]
    [IsScalarTower K W.toAffine.CoordinateRing S] [IsLocalization P.primeCompl S] :
    ¬ Algebra.FormallyUnramified K S := by
  obtain ⟨e⟩ := dual_lifts_of_nonsingular W x y h
  let a := e.symm 0
  let b := e.symm 1
  have hNe : a ≠ b := fun he => zero_ne_one (e.symm.injective he)
  exact LocalizedDualLiftObstruction.not_formally_unramified_of_local_lifts
    (residueAt W x y hEq) P hP S (dualEvaluation W x y a) (dualEvaluation W x y b)
    (dualEvaluation_residue W x y hEq a) (dualEvaluation_residue W x y hEq b)
    (fun he => hNe (dualEvaluation_injective W x y he))

end
end ManuscriptAudit.Paper2WeierstrassNotUnramified

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassNotUnramified.dualEvaluation_residue,
      ``ManuscriptAudit.Paper2WeierstrassNotUnramified.dualEvaluation_injective,
      ``ManuscriptAudit.Paper2WeierstrassNotUnramified.not_formally_unramified,
      ``ManuscriptAudit.Paper2WeierstrassNotUnramified.local_not_formally_unramified] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
