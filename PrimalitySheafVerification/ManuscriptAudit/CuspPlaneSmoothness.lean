import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta

/-!
The integral cusp from Paper 2 fails the infinitesimal lifting criterion.
Its coordinate equation is the same presentation used to compute the
normalization and the cotangent homology.
-/

namespace ManuscriptAudit.CuspPlaneSmoothness

open Polynomial CuspDelta

noncomputable section

variable (K : Type*) [Field K]

private abbrev Curve := AdjoinRoot (cuspPlaneEquation K)

private abbrev xCoord : Curve K := AdjoinRoot.of (cuspPlaneEquation K) Polynomial.X

private abbrev yCoord : Curve K := AdjoinRoot.root (cuspPlaneEquation K)

private theorem coordinate_relation : yCoord K ^ 2 = xCoord K ^ 3 := by
  have h : AdjoinRoot.mk (cuspPlaneEquation K) (cuspPlaneEquation K) = 0 := by
    rw [AdjoinRoot.mk_self]
  change AdjoinRoot.mk (cuspPlaneEquation K)
    (Polynomial.X ^ 2 - Polynomial.C ((Polynomial.X : Polynomial K) ^ 3)) = 0 at h
  rw [map_sub, map_pow] at h
  change yCoord K ^ 2 - AdjoinRoot.of (cuspPlaneEquation K) (Polynomial.X ^ 3) = 0 at h
  rw [map_pow] at h
  exact sub_eq_zero.mp h

section Evaluation

variable {B : Type*} [CommRing B] [Algebra K B]

private theorem evaluate_equation (x y : B) (h : y ^ 2 = x ^ 3) :
    (cuspPlaneEquation K).eval₂ (Polynomial.aeval x).toRingHom y = 0 := by
  have hx : (Polynomial.aeval x : Polynomial K →ₐ[K] B).toRingHom Polynomial.X = x :=
    Polynomial.aeval_X
  simpa only [cuspPlaneEquation, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_pow, hx] using sub_eq_zero.mpr h

private def evaluateCusp (x y : B) (h : y ^ 2 = x ^ 3) : Curve K →ₐ[K] B :=
  AdjoinRoot.liftAlgHom (cuspPlaneEquation K) (Polynomial.aeval x) y
    (evaluate_equation K x y h)

private theorem evaluateCusp_x (x y : B) (h : y ^ 2 = x ^ 3) :
    evaluateCusp K x y h (xCoord K) = x := by
  calc
    _ = (Polynomial.aeval x : Polynomial K →ₐ[K] B) Polynomial.X :=
      AdjoinRoot.liftAlgHom_of (cuspPlaneEquation K) (Polynomial.aeval x) y
        (evaluate_equation K x y h) Polynomial.X
    _ = x := Polynomial.aeval_X

private theorem evaluateCusp_y (x y : B) (h : y ^ 2 = x ^ 3) :
    evaluateCusp K x y h (yCoord K) = y :=
  AdjoinRoot.liftAlgHom_root (cuspPlaneEquation K) (Polynomial.aeval x) y
    (evaluate_equation K x y h)

end Evaluation

set_option maxHeartbeats 1200000 in
private theorem not_formallySmooth_from_truncation {B : Type*} [CommRing B] [Algebra K B]
    (t : B) (ht₄ : t ^ 4 = 0) (ht₃ : t ^ 3 ≠ 0) : ¬ Algebra.FormallySmooth K (Curve K) := by
  intro hs
  letI : Algebra.FormallySmooth K (Curve K) := hs
  let J : Ideal B := Ideal.span {t ^ 3}
  let q : B →ₐ[K] B ⧸ J := Ideal.Quotient.mkₐ K J
  have hJ : J ^ 2 = ⊥ := by
    have hnil : (t ^ 3) ^ 2 = 0 := by
      rw [← pow_mul, show 3 * 2 = 4 + 2 by decide, pow_add, ht₄, zero_mul]
    change (Ideal.span ({t ^ 3} : Set B)) ^ 2 = ⊥
    rw [Ideal.span_singleton_pow, hnil]
    simp
  have hAnn {a : B} (ha : a ∈ J) : t * a = 0 := by
    change a ∈ Ideal.span ({t ^ 3} : Set B) at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    calc
      t * (t ^ 3 * b) = (t ^ 3 * t) * b := by ac_rfl
      _ = t ^ 4 * b := by rw [pow_succ t 3]
      _ = 0 := by rw [ht₄, zero_mul]
  have hSq {a : B} (ha : a ∈ J) : a ^ 2 = 0 := by
    have hm : a * a ∈ J * J := Ideal.mul_mem_mul ha ha
    rw [← pow_two J, hJ, Ideal.mem_bot] at hm
    simpa only [pow_two] using hm
  have hqt : (q t) ^ 3 = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hred : (0 : B ⧸ J) ^ 2 = (q t) ^ 3 := by
    rw [hqt, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  let φ : Curve K →ₐ[K] B ⧸ J := evaluateCusp K (q t) 0 hred
  obtain ⟨lift, hlift⟩ := Algebra.FormallySmooth.comp_surjective K (Curve K) J hJ φ
  have hx : q (lift (xCoord K)) = q t := by
    calc
      _ = φ (xCoord K) := AlgHom.congr_fun hlift _
      _ = _ := evaluateCusp_x K (q t) 0 hred
  have hy : q (lift (yCoord K)) = 0 := by
    calc
      _ = φ (yCoord K) := AlgHom.congr_fun hlift _
      _ = _ := evaluateCusp_y K (q t) 0 hred
  let d := lift (xCoord K) - t
  have hd : d ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q d = 0
    simp only [d, map_sub, hx, sub_self]
  have hyJ : lift (yCoord K) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp hy
  have hx₂ : (t + d) ^ 2 = t ^ 2 := by
    calc
      _ = t ^ 2 + 2 * (t * d) + d ^ 2 := by ring
      _ = _ := by rw [hAnn hd, hSq hd, mul_zero, add_zero, add_zero]
  have hx₃ : (t + d) ^ 3 = t ^ 3 := by
    have htd : t ^ 2 * d = 0 := by rw [pow_two, mul_assoc, hAnn hd, mul_zero]
    calc
      _ = (t + d) ^ 2 * (t + d) := pow_succ _ 2
      _ = t ^ 2 * t := by rw [hx₂, mul_add, htd, add_zero]
      _ = _ := (pow_succ t 2).symm
  have hxLift : lift (xCoord K) ^ 3 = t ^ 3 := by
    have hsum : lift (xCoord K) = t + d := by dsimp [d]; ring
    exact (congrArg (fun a : B => a ^ 3) hsum).trans hx₃
  have hcusp := congrArg lift (coordinate_relation K)
  rw [map_pow, map_pow, hSq hyJ, hxLift] at hcusp
  exact ht₃ hcusp.symm

/-- The integral plane cusp is never formally smooth over its field. -/
theorem cuspPlane_not_formallySmooth :
    ¬ Algebra.FormallySmooth K (AdjoinRoot (cuspPlaneEquation K)) := by
  let I : Ideal (Polynomial K) := Ideal.span {(Polynomial.X : Polynomial K) ^ 4}
  let t : Polynomial K ⧸ I := Ideal.Quotient.mk I Polynomial.X
  have ht₄ : t ^ 4 = 0 := by
    change (Ideal.Quotient.mk I (Polynomial.X : Polynomial K)) ^ 4 = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have ht₃ : t ^ 3 ≠ 0 := by
    intro h
    change (Ideal.Quotient.mk I (Polynomial.X : Polynomial K)) ^ 3 = 0 at h
    rw [← map_pow] at h
    have hdiv : (Polynomial.X : Polynomial K) ^ 4 ∣ Polynomial.X ^ 3 :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp hdiv) 3 (by decide)
    have he : (1 : K) = 0 := by simpa using hcoeff
    exact one_ne_zero he
  exact not_formallySmooth_from_truncation K t ht₄ ht₃

/-- The actual integral cusp is singular over every field. -/
theorem cuspPlane_not_smooth : ¬ Algebra.Smooth K (AdjoinRoot (cuspPlaneEquation K)) :=
  fun hs => cuspPlane_not_formallySmooth K hs.formallySmooth

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``cuspPlane_not_formallySmooth, ``cuspPlane_not_smooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.CuspPlaneSmoothness
