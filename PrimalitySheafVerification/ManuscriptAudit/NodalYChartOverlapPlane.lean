import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveClosure
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartOverlap

/-! The two normalized parametrizations of the nodal cubic agree in the
actual projective plane on their common open chart. -/

namespace ManuscriptAudit.NodalYChartOverlapPlane

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspProperCompactification
  (affineZChartι standardZChartRing standardZChartEvaluation standardZChartEvaluation_mk)
open CuspYChartAlgebra (PlaneRing grading plane y z X_mem_one YChartRing yChartι
  fractionEvaluation fractionEvaluation_mk aeval_scale)
open NodalProjectiveClosure (affineNode nodeInPlane chartValues chartValues_Z chartEvaluation)
open NodalYChartImmersion (nodeYChart nodeToYChart nodeYInPlane evalYChart evalYChart_mk
  evalYPolynomial yValues xCoeff zCoeff)
open NodalYChartOverlap (parameterRing t tInv denominatorInv denominator_image
  denominator_mul_inv yToParameter yToParameter_x yToParameter_z)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

/-- The map from the affine nodal algebra to the localized normalization. -/
def zParameter : NodalConductor.coordinates K →ₐ[K] parameterRing K :=
  (Algebra.algHom K (Polynomial K) (parameterRing K)).comp (NodalConductor.coordinates K).val

private theorem zParameter_x :
    zParameter K (NodalAffinePresentation.nodeX K) = t K ^ 2 - 1 := by
  change algebraMap (Polynomial K) (parameterRing K) (NodalConductor.x K) = _
  rw [NodalConductor.x, map_sub, map_pow, map_one] <;> rfl

private theorem zParameter_y :
    zParameter K (NodalAffinePresentation.nodeY K) = t K * (t K ^ 2 - 1) :=
  denominator_image K

private def zValues (i : Fin 3) : parameterRing K :=
  if i = 0 then t K ^ 2 - 1 else if i = 1 then t K * (t K ^ 2 - 1) else 1

private def evalZParameter : PlaneRing K →ₐ[K] parameterRing K :=
  MvPolynomial.aeval (zValues K)

private theorem evalZParameter_y : evalZParameter K (y K) = t K * (t K ^ 2 - 1) := by
  simp [evalZParameter, zValues, y]

private theorem evalZParameter_z : evalZParameter K (z K) = 1 := by
  simp [evalZParameter, zValues, z]

abbrev yz := y K * z K
abbrev YZChartRing := Away (grading K) (yz K)

private theorem evalYZ_mul_inv : evalZParameter K (yz K) * denominatorInv K = 1 := by
  change evalZParameter K (y K * z K) * denominatorInv K = 1
  rw [map_mul, evalZParameter_y, evalZParameter_z, mul_one]
  exact denominator_mul_inv K

def evalYZ : YZChartRing K →+* parameterRing K :=
  fractionEvaluation K (evalZParameter K).toRingHom (yz K) (denominatorInv K) (evalYZ_mul_inv K)

def zToYZ : standardZChartRing K →+* YZChartRing K :=
  awayMap (grading K) (X_mem_one K 1) (show yz K = z K * y K from mul_comm _ _)

def yToYZ : YChartRing K →+* YZChartRing K :=
  awayMap (grading K) (X_mem_one K 2) (show yz K = y K * z K from rfl)

private theorem affine_eval_param_mk (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • 1)) :
    zParameter K (chartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp)) =
      evalZParameter K p := by
  unfold chartEvaluation
  rw [standardZChartEvaluation_mk]
  change ((zParameter K).comp (MvPolynomial.aeval (chartValues K))) p =
    MvPolynomial.aeval (zValues K) p
  rw [MvPolynomial.comp_aeval]
  apply congrArg (fun v : Fin 3 → parameterRing K => MvPolynomial.aeval v p)
  funext i
  fin_cases i
  · change zParameter K (NodalAffinePresentation.nodeX K) = t K ^ 2 - 1
    exact zParameter_x K
  · change zParameter K (NodalAffinePresentation.nodeY K) = t K * (t K ^ 2 - 1)
    exact zParameter_y K
  · change zParameter K 1 = 1
    exact map_one _

private theorem scaled_values :
    (fun i => (t K * (t K ^ 2 - 1)) * yToParameter K (yValues K i)) = zValues K := by
  funext i
  fin_cases i
  · change (t K * (t K ^ 2 - 1)) * yToParameter K (xCoeff K) = t K ^ 2 - 1
    rw [yToParameter_x]
    calc
      _ = (t K ^ 2 - 1) * ((t K * (t K ^ 2 - 1)) * denominatorInv K) := by
        unfold tInv
        ring
      _ = _ := by rw [denominator_mul_inv, mul_one]
  · change (t K * (t K ^ 2 - 1)) * yToParameter K 1 = t K * (t K ^ 2 - 1)
    rw [map_one, mul_one]
  · change (t K * (t K ^ 2 - 1)) * yToParameter K (zCoeff K) = 1
    rw [yToParameter_z, denominator_mul_inv]

private theorem scaled_eval (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K n) :
    evalZParameter K p = (t K * (t K ^ 2 - 1)) ^ n * yToParameter K (evalYPolynomial K p) := by
  unfold evalZParameter
  rw [← scaled_values K, aeval_scale K _ _ hp]
  congr 1
  change _ = ((yToParameter K).comp (MvPolynomial.aeval (yValues K))) p
  rw [MvPolynomial.comp_aeval]

theorem evalYZ_on_z :
    (evalYZ K).comp (zToYZ K) = (zParameter K).toRingHom.comp (chartEvaluation K) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (grading K) (X_mem_one K 2) b
  change evalYZ K (zToYZ K (Away.mk (grading K) (X_mem_one K 2) n p hp)) =
    zParameter K (chartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp))
  unfold zToYZ
  rw [awayMap_mk, affine_eval_param_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZParameter K (p * y K ^ n) * denominatorInv K ^ n = evalZParameter K p
  rw [map_mul, map_pow, evalZParameter_y, mul_assoc, ← mul_pow, denominator_mul_inv,
    one_pow, mul_one]

theorem evalYZ_on_y :
    (evalYZ K).comp (yToYZ K) = (yToParameter K).toRingHom.comp (evalYChart K) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (grading K) (X_mem_one K 1) b
  change evalYZ K (yToYZ K (Away.mk (grading K) (X_mem_one K 1) n p hp)) =
    yToParameter K (evalYChart K (Away.mk (grading K) (X_mem_one K 1) n p hp))
  unfold yToYZ
  rw [awayMap_mk, evalYChart_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZParameter K (p * z K ^ n) * denominatorInv K ^ n =
    yToParameter K (evalYPolynomial K p)
  rw [map_mul, map_pow, evalZParameter_z, one_pow, mul_one]
  have hp' : p ∈ grading K n := by
    have hd : n • (1 : ℕ) = n := by simp
    rw [← hd]
    exact hp
  rw [scaled_eval K n p hp']
  calc
    _ = yToParameter K (evalYPolynomial K p) *
          ((t K * (t K ^ 2 - 1)) ^ n * denominatorInv K ^ n) := by ac_rfl
    _ = _ := by rw [← mul_pow, denominator_mul_inv, one_pow, mul_one]

abbrev parameterScheme : Scheme.{u} := Spec (CommRingCat.of (parameterRing K))

def toAffineNode : parameterScheme K ⟶ affineNode K :=
  Spec.map (CommRingCat.ofHom (zParameter K).toRingHom)

def toNodeYChart : parameterScheme K ⟶ nodeYChart K :=
  Spec.map (CommRingCat.ofHom (yToParameter K).toRingHom)

private def yzChartι : Spec (CommRingCat.of (YZChartRing K)) ⟶ plane K :=
  Proj.awayι (grading K) (yz K) (SetLike.mul_mem_graded (X_mem_one K 1) (X_mem_one K 2))
    (by decide)

/-- The two open-chart parametrizations are the same actual map to the projective plane. -/
theorem plane_overlap_eq :
    toAffineNode K ≫ nodeInPlane K = toNodeYChart K ≫ nodeYInPlane K := by
  have hZ :
      toAffineNode K ≫ Spec.map (CommRingCat.ofHom (chartEvaluation K)) =
        Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ Spec.map (CommRingCat.ofHom (zToYZ K)) := by
    unfold toAffineNode
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_z K).symm)
  have hY :
      toNodeYChart K ≫ nodeToYChart K =
        Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ Spec.map (CommRingCat.ofHom (yToYZ K)) := by
    unfold toNodeYChart nodeToYChart
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_y K).symm)
  calc
    _ = Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ yzChartι K := by
      unfold nodeInPlane
      rw [← Category.assoc, hZ, Category.assoc]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ f)
        (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 2) (by decide)
          (X_mem_one K 1) (show yz K = z K * y K from mul_comm _ _))
    _ = _ := by
      symm
      unfold nodeYInPlane
      rw [← Category.assoc, hY, Category.assoc]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ f)
        (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 1) (by decide)
          (X_mem_one K 2) (show yz K = y K * z K from rfl))

end

end ManuscriptAudit.NodalYChartOverlapPlane

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalYChartOverlapPlane.evalYZ_on_z,
      ``ManuscriptAudit.NodalYChartOverlapPlane.evalYZ_on_y,
      ``ManuscriptAudit.NodalYChartOverlapPlane.plane_overlap_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
