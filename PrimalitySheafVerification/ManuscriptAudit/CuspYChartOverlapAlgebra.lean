import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartAlgebra

/-!
The degree-zero maps from the two cusp charts into the Laurent
polynomial ring agree after passing through the common plane chart
where both coordinates are invertible.
-/

namespace ManuscriptAudit.CuspYChartOverlapAlgebra

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspPunctured CuspProperCompactification CuspYChartAlgebra

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 512

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K]

abbrev LaurentRing := LaurentPolynomial K
abbrev yz := y K * z K
abbrev YZChartRing := Away (grading K) (yz K)
private abbrev ZChartRing := Away (grading K) (z K)

def cuspLaurent : CuspSubalgebra K →ₐ[K] LaurentRing K :=
  Polynomial.toLaurentAlg.comp (CuspSubalgebra K).val

def lineLaurent : Polynomial K →ₐ[K] LaurentRing K :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

private def zValues (i : Fin 3) : LaurentRing K :=
  if i = 0 then LaurentPolynomial.T 2 else if i = 1 then LaurentPolynomial.T 3 else 1

private def evalZLaurent : PlaneRing K →ₐ[K] LaurentRing K :=
  MvPolynomial.aeval (zValues K)

private theorem evalZLaurent_y : evalZLaurent K (y K) = LaurentPolynomial.T 3 := by
  simp [evalZLaurent, zValues, y]

private theorem evalZLaurent_z : evalZLaurent K (z K) = 1 := by
  simp [evalZLaurent, zValues, z]

private theorem mul_T_three_neg_three :
    (LaurentPolynomial.T 3 : LaurentRing K) * LaurentPolynomial.T (-3) = 1 := by
  rw [← LaurentPolynomial.T_add]
  norm_num

private theorem evalYZ_mul_inv :
    evalZLaurent K (yz K) * LaurentPolynomial.T (-3) = 1 := by
  rw [map_mul, evalZLaurent_y, evalZLaurent_z, mul_one]
  exact mul_T_three_neg_three K

def evalYZ : YZChartRing K →+* LaurentRing K :=
  fractionEvaluation K (evalZLaurent K).toRingHom (yz K) (LaurentPolynomial.T (-3))
    (evalYZ_mul_inv K)

def yToYZ : YChartRing K →+* YZChartRing K :=
  awayMap (grading K) (X_mem_one K 2) (show yz K = y K * z K from rfl)

def zToYZ : ZChartRing K →+* YZChartRing K :=
  awayMap (grading K) (X_mem_one K 1) (show yz K = z K * y K from mul_comm _ _)

private theorem affine_eval_laurent_mk (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • 1)) :
    cuspLaurent K (affineChartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp)) =
      evalZLaurent K p := by
  change Polynomial.toLaurentAlg
    ((affineChartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp)) : Polynomial K) = _
  rw [affineChartEvaluation_mk_coe]
  change ((Polynomial.toLaurentAlg : Polynomial K →ₐ[K] LaurentRing K).comp
    (MvPolynomial.aeval (fun i : Fin 3 => if i = 0 then Polynomial.X ^ 2
      else if i = 1 then Polynomial.X ^ 3 else 1))) p = MvPolynomial.aeval (zValues K) p
  rw [MvPolynomial.comp_aeval]
  apply congrArg (fun v : Fin 3 → LaurentRing K => MvPolynomial.aeval v p)
  funext i
  fin_cases i <;> simp [zValues, Polynomial.toLaurent_X_pow]

private theorem scaled_values :
    (fun i => (LaurentPolynomial.T 3 : LaurentRing K) * lineLaurent K (yValues K i)) = zValues K := by
  funext i
  fin_cases i <;>
    norm_num [lineLaurent, yValues, zValues, Polynomial.toLaurent_X_pow, ← LaurentPolynomial.T_add]

private theorem scaled_eval (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K n) :
    evalZLaurent K p = (LaurentPolynomial.T 3 : LaurentRing K) ^ n * lineLaurent K (evalYPolynomial K p) := by
  unfold evalZLaurent
  rw [← scaled_values K, aeval_scale K _ _ hp]
  congr 1
  change _ = ((lineLaurent K).comp (MvPolynomial.aeval (yValues K))) p
  rw [MvPolynomial.comp_aeval]

theorem evalYZ_on_z :
    (evalYZ K).comp (zToYZ K) = (cuspLaurent K).toRingHom.comp (affineChartEvaluation K) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (X_mem_one K 2) b
  change evalYZ K (zToYZ K (Away.mk (grading K) (X_mem_one K 2) n p hp)) =
    cuspLaurent K (affineChartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp))
  unfold zToYZ
  rw [awayMap_mk, affine_eval_laurent_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZLaurent K (p * y K ^ n) * LaurentPolynomial.T (-3) ^ n = evalZLaurent K p
  rw [map_mul, map_pow, evalZLaurent_y, mul_assoc, ← mul_pow, mul_T_three_neg_three, one_pow, mul_one]

theorem evalYZ_on_y :
    (evalYZ K).comp (yToYZ K) = (lineLaurent K).toRingHom.comp (evalYChart K) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (X_mem_one K 1) b
  change evalYZ K (yToYZ K (Away.mk (grading K) (X_mem_one K 1) n p hp)) =
    lineLaurent K (evalYChart K (Away.mk (grading K) (X_mem_one K 1) n p hp))
  unfold yToYZ
  rw [awayMap_mk, evalYChart_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZLaurent K (p * z K ^ n) * LaurentPolynomial.T (-3) ^ n =
    lineLaurent K (evalYPolynomial K p)
  rw [map_mul, map_pow, evalZLaurent_z, one_pow, mul_one]
  rw [scaled_eval K n p (by simpa only [nsmul_eq_mul, mul_one] using hp)]
  calc
    _ = lineLaurent K (evalYPolynomial K p) *
          ((LaurentPolynomial.T 3 : LaurentRing K) ^ n * LaurentPolynomial.T (-3) ^ n) := by ac_rfl
    _ = _ := by rw [← mul_pow, mul_T_three_neg_three, one_pow, mul_one]


end

end ManuscriptAudit.CuspYChartOverlapAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspYChartOverlapAlgebra.evalYZ_on_z,
      ``ManuscriptAudit.CuspYChartOverlapAlgebra.evalYZ_on_y] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
