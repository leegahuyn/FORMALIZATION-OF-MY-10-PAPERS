import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveClosure
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartImmersion
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartOverlap

/-! The Weierstrass Y and Z charts have the same map to the actual plane on their overlap. -/

namespace ManuscriptAudit.WeierstrassInfinityOverlapPlane

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspProperCompactification (affineZChartι standardZChartRing standardZChartEvaluation_mk)
open CuspYChartAlgebra (PlaneRing grading plane y z X_mem_one YChartRing yChartι
  fractionEvaluation fractionEvaluation_mk aeval_scale)
open WeierstrassInfinityChartOverlap (A ZOverlap C₀ zx zy zInv zy_mul_zInv toZChart toZChart_x toZChart_z)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

def localizeAffine : A W →ₐ[K] ZOverlap W :=
  Algebra.algHom K (A W) (ZOverlap W)

private def zValues (i : Fin 3) : ZOverlap W :=
  if i = 0 then zx W else if i = 1 then zy W else 1

private def evalZ : PlaneRing K →ₐ[K] ZOverlap W := MvPolynomial.aeval (zValues W)

private theorem evalZ_y : evalZ W (y K) = zy W := by simp [evalZ, zValues, y]
private theorem evalZ_z : evalZ W (z K) = 1 := by simp [evalZ, zValues, z]

abbrev yz := y K * z K
abbrev YZChartRing := Away (grading K) (yz (K := K))

private theorem evalYZ_mul_inv : evalZ W (yz (K := K)) * zInv W = 1 := by
  change evalZ W (y K * z K) * zInv W = 1
  rw [map_mul, evalZ_y, evalZ_z, mul_one, zy_mul_zInv]

def evalYZ : YZChartRing (K := K) →+* ZOverlap W :=
  fractionEvaluation K (evalZ W).toRingHom (yz (K := K)) (zInv W) (evalYZ_mul_inv W)

def zToYZ : standardZChartRing K →+* YZChartRing (K := K) :=
  awayMap (grading K) (X_mem_one K 1) (show yz (K := K) = z K * y K from mul_comm _ _)

def yToYZ : YChartRing K →+* YZChartRing (K := K) :=
  awayMap (grading K) (X_mem_one K 2) (show yz (K := K) = y K * z K from rfl)

private theorem affine_eval_localized_mk (n : ℕ) (p : PlaneRing K)
    (hp : p ∈ grading K (n • 1)) :
    localizeAffine W (WeierstrassProjectiveClosure.chartEvaluation W
      (Away.mk (grading K) (X_mem_one K 2) n p hp)) = evalZ W p := by
  unfold WeierstrassProjectiveClosure.chartEvaluation
  rw [standardZChartEvaluation_mk]
  change ((localizeAffine W).comp (MvPolynomial.aeval (WeierstrassProjectiveClosure.chartValues W))) p =
    MvPolynomial.aeval (zValues W) p
  rw [MvPolynomial.comp_aeval]
  apply congrArg (fun v : Fin 3 → ZOverlap W => MvPolynomial.aeval v p)
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact map_one _

private theorem scaled_values :
    (fun i => zy W * toZChart W (WeierstrassInfinityChartImmersion.values W i)) = zValues W := by
  funext i
  fin_cases i
  · change zy W * toZChart W (WeierstrassInfinityChartAlgebra.x W) = zx W
    rw [toZChart_x, mul_left_comm, zy_mul_zInv, mul_one]
  · change zy W * toZChart W 1 = zy W
    rw [map_one, mul_one]
  · change zy W * toZChart W (WeierstrassInfinityChartAlgebra.z W) = 1
    rw [toZChart_z, zy_mul_zInv]

private theorem scaled_eval (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K n) :
    evalZ W p = zy W ^ n * toZChart W (WeierstrassInfinityChartImmersion.evaluation W p) := by
  unfold evalZ
  rw [← scaled_values W, aeval_scale K _ _ hp]
  congr 1
  change _ = ((toZChart W).comp (MvPolynomial.aeval (WeierstrassInfinityChartImmersion.values W))) p
  rw [MvPolynomial.comp_aeval]

set_option maxHeartbeats 1000000 in
theorem evalYZ_on_z :
    (evalYZ W).comp (zToYZ (K := K)) =
      (localizeAffine W).toRingHom.comp (WeierstrassProjectiveClosure.chartEvaluation W) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (grading K) (X_mem_one K 2) b
  change evalYZ W (zToYZ (Away.mk (grading K) (X_mem_one K 2) n p hp)) =
    localizeAffine W (WeierstrassProjectiveClosure.chartEvaluation W
      (Away.mk (grading K) (X_mem_one K 2) n p hp))
  unfold zToYZ
  rw [awayMap_mk, affine_eval_localized_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZ W (p * y K ^ n) * zInv W ^ n = evalZ W p
  rw [map_mul, map_pow, evalZ_y, mul_assoc, ← mul_pow, zy_mul_zInv, one_pow, mul_one]

set_option maxHeartbeats 1000000 in
theorem evalYZ_on_y :
    (evalYZ W).comp (yToYZ (K := K)) =
      (toZChart W).toRingHom.comp (WeierstrassInfinityChartImmersion.chartEvaluation W) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (grading K) (X_mem_one K 1) b
  change evalYZ W (yToYZ (Away.mk (grading K) (X_mem_one K 1) n p hp)) =
    toZChart W (WeierstrassInfinityChartImmersion.chartEvaluation W
      (Away.mk (grading K) (X_mem_one K 1) n p hp))
  unfold yToYZ
  rw [awayMap_mk, WeierstrassInfinityChartImmersion.chartEvaluation_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZ W (p * z K ^ n) * zInv W ^ n =
    toZChart W (WeierstrassInfinityChartImmersion.evaluation W p)
  rw [map_mul, map_pow, evalZ_z, one_pow, mul_one]
  have hp' : p ∈ grading K n := by simpa using hp
  rw [scaled_eval W n p hp']
  calc
    _ = toZChart W (WeierstrassInfinityChartImmersion.evaluation W p) *
          ((zy W) ^ n * (zInv W) ^ n) := by ac_rfl
    _ = _ := by rw [← mul_pow, zy_mul_zInv, one_pow, mul_one]

abbrev overlapScheme : Scheme.{u} := Spec (CommRingCat.of (ZOverlap W))

def toAffine : overlapScheme W ⟶ WeierstrassProjectiveClosure.affineScheme W :=
  Spec.map (CommRingCat.ofHom (localizeAffine W).toRingHom)

def toInfinityChart : overlapScheme W ⟶ WeierstrassInfinityChartImmersion.chartScheme W :=
  Spec.map (CommRingCat.ofHom (toZChart W).toRingHom)

private def yzChartι : Spec (CommRingCat.of (YZChartRing (K := K))) ⟶ plane K :=
  Proj.awayι (grading K) (yz (K := K))
    (SetLike.mul_mem_graded (X_mem_one K 1) (X_mem_one K 2)) (by decide)

/-- Both normalized coordinate presentations give the same morphism into projective space. -/
theorem plane_overlap_eq :
    toAffine W ≫ WeierstrassProjectiveClosure.inPlane W =
      toInfinityChart W ≫ WeierstrassInfinityChartImmersion.inPlane W := by
  have hZ :
      toAffine W ≫ Spec.map (CommRingCat.ofHom (WeierstrassProjectiveClosure.chartEvaluation W)) =
        Spec.map (CommRingCat.ofHom (evalYZ W)) ≫ Spec.map (CommRingCat.ofHom (zToYZ (K := K))) := by
    unfold toAffine
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_z W).symm)
  have hY :
      toInfinityChart W ≫ WeierstrassInfinityChartImmersion.toYChart W =
        Spec.map (CommRingCat.ofHom (evalYZ W)) ≫ Spec.map (CommRingCat.ofHom (yToYZ (K := K))) := by
    unfold toInfinityChart WeierstrassInfinityChartImmersion.toYChart
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_y W).symm)
  calc
    _ = Spec.map (CommRingCat.ofHom (evalYZ W)) ≫ yzChartι (K := K) := by
      unfold WeierstrassProjectiveClosure.inPlane
      rw [← Category.assoc, hZ, Category.assoc]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ W)) ≫ f)
        (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 2) (by decide)
          (X_mem_one K 1) (show yz (K := K) = z K * y K from mul_comm _ _))
    _ = _ := by
      symm
      unfold WeierstrassInfinityChartImmersion.inPlane
      rw [← Category.assoc, hY, Category.assoc]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ W)) ≫ f)
        (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 1) (by decide)
          (X_mem_one K 2) (show yz (K := K) = y K * z K from rfl))

end

end ManuscriptAudit.WeierstrassInfinityOverlapPlane

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityOverlapPlane.evalYZ_on_z,
      ``ManuscriptAudit.WeierstrassInfinityOverlapPlane.evalYZ_on_y,
      ``ManuscriptAudit.WeierstrassInfinityOverlapPlane.plane_overlap_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
