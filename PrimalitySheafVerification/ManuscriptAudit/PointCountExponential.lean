import Lean.Util.CollectAxioms
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Exponential point-count series over an arbitrary field of characteristic zero. -/

namespace ManuscriptAudit.PointCountExponential

open PowerSeries

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev Series (K : Type*) := K⟦X⟧

def countLog (counts : Series K) : Series K :=
  PowerSeries.mk fun n => if n = 0 then 0 else coeff n counts / (n : K)

def expAt (f : Series K) : Series K :=
  (PowerSeries.exp K).subst f

/-- The exponential zeta series obtained from the positive-degree point counts. -/
def zetaOfCountSeries (counts : Series K) : Series K :=
  expAt (countLog counts)

theorem countLog_constantCoeff (counts : Series K) :
    constantCoeff (countLog counts) = 0 := by
  simp [countLog, constantCoeff_mk]

theorem X_mul_derivative_countLog (counts : Series K) (hc : constantCoeff counts = 0) :
    X * derivative K (countLog counts) = counts := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, hc]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, countLog, coeff_mk, if_neg n.succ_ne_zero]
    simp only [Nat.cast_add, Nat.cast_one]
    exact div_mul_cancel₀ _ (by
      simpa only [Nat.cast_add, Nat.cast_one] using (Nat.cast_ne_zero.mpr n.succ_ne_zero : (n.succ : K) ≠ 0))

theorem expAt_constantCoeff (f : Series K) (hf : constantCoeff f = 0) :
    constantCoeff (expAt f) = 1 := by
  have hSubst : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  have hOther (j : ℕ) (hj : j ≠ 0) :
      coeff j (PowerSeries.exp K) • coeff 0 (f ^ j) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hf, zero_pow hj, smul_zero]
  change constantCoeff ((PowerSeries.exp K).subst f) = 1
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hSubst, finsum_eq_single _ 0 hOther] <;>
    simp [coeff_zero_eq_constantCoeff_apply]

theorem derivative_expAt (f : Series K) (hf : constantCoeff f = 0) :
    derivative K (expAt f) = expAt f * derivative K f := by
  have hSubst : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  unfold expAt
  first
  | rw [derivative_subst K hSubst, derivative_exp K]
  | rw [derivative_subst hSubst, derivative_exp K]

theorem derivative_one : derivative K (1 : Series K) = 0 :=
  PowerSeries.derivativeFun_one

theorem eq_of_same_derivative_factor {F G W : Series K}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    (dF : derivative K F = F * W) (dG : derivative K G = G * W) :
    F = G := by
  have hn : constantCoeff G ≠ 0 := by
    rw [hG]
    exact one_ne_zero
  have hInv := PowerSeries.mul_inv_cancel G hn
  have hD : derivative K (F * G⁻¹) = derivative K (1 : Series K) := by
    rw [derivative_one, Derivation.leibniz, derivative_inv', dF, dG]
    simp only [smul_eq_mul]
    linear_combination -(F * G⁻¹ * W) * hInv
  have hC : constantCoeff (F * G⁻¹) = constantCoeff (1 : Series K) := by
    simp only [map_mul, constantCoeff_inv, hF, hG, inv_one, mul_one, map_one]
  have h := PowerSeries.derivative.ext hD hC
  calc
    F = F * (G⁻¹ * G) := by rw [PowerSeries.inv_mul_cancel G hn, mul_one]
    _ = (F * G⁻¹) * G := by rw [mul_assoc]
    _ = G := by rw [h, one_mul]

/-- The geometric power series with successive coefficients qⁿ. -/
def geometric (q : K) : Series K := PowerSeries.mk fun n => q ^ n

theorem one_sub_mul_geometric (q : K) :
    (1 - (X : Series K) * C q) * geometric q = 1 := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, mul_assoc]
  cases n with
  | zero =>
    simp only [map_sub, geometric, coeff_mk, pow_zero, coeff_zero_X_mul, sub_zero, coeff_zero_one]
  | succ n =>
    simp only [map_sub, coeff_succ_X_mul, coeff_C_mul, geometric, coeff_mk,
      coeff_one, Nat.succ_ne_zero, if_false]
    rw [pow_succ, mul_comm (q ^ n) q, sub_self]

/-- The linear denominator associated with one geometric ratio. -/
def linearFactor (c : K) : Series K := 1 - X * C c

theorem linearFactor_const (c : K) : constantCoeff (linearFactor c) = 1 := by
  simp [linearFactor]

theorem geometric_const (c : K) : constantCoeff (geometric c) = 1 := by
  simp [geometric, constantCoeff_mk]

theorem geometric_eq_inv (c : K) : geometric c = (linearFactor c)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one (by simp [linearFactor] : constantCoeff (linearFactor c) ≠ 0)).2
  simpa only [mul_comm, linearFactor] using one_sub_mul_geometric c

theorem derivative_linearFactor (c : K) :
    derivative K (linearFactor c) = linearFactor c * (-(C c * geometric c)) := by
  have hF : derivative K (linearFactor c) = -C c := by
    rw [linearFactor, map_sub, derivative_one, Derivation.leibniz]
    simp [smul_eq_mul]
  rw [hF]
  have h := one_sub_mul_geometric c
  change linearFactor c * geometric c = 1 at h
  linear_combination C c * h

theorem derivative_geometric (c : K) :
    derivative K (geometric c) = geometric c * (C c * geometric c) := by
  have h : derivative K (linearFactor c) = -C c := by
    rw [linearFactor, map_sub, derivative_one, Derivation.leibniz]
    simp [smul_eq_mul]
  rw [geometric_eq_inv c, derivative_inv', h]
  ring

theorem derivative_product {A B a b : Series K}
    (hA : derivative K A = A * a) (hB : derivative K B = B * b) :
    derivative K (A * B) = (A * B) * (a + b) := by
  rw [Derivation.leibniz, hA, hB]
  simp only [smul_eq_mul]
  ring

/-- Actual power sums in the given degree sequence for one reciprocal pair. -/
def twoRootCounts (q α β : K) : Series K :=
  X * PowerSeries.mk (fun n => q ^ (n + 1) + 1 - α ^ (n + 1) - β ^ (n + 1))

theorem twoRootCounts_zeta (q α β : K) :
    zetaOfCountSeries (twoRootCounts q α β) =
      (linearFactor α * linearFactor β) * (geometric 1 * geometric q) := by
  let H := C (1 : K) * geometric 1 + C q * geometric q -
    C α * geometric α - C β * geometric β
  have hH : derivative K (countLog (twoRootCounts q α β)) = H := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero : (X : Series K) ≠ 0)
    rw [X_mul_derivative_countLog (twoRootCounts q α β) (by simp [twoRootCounts])]
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [twoRootCounts, H, coeff_zero_X_mul]
    | succ n =>
      simp only [twoRootCounts, H, coeff_succ_X_mul, map_sub, map_add, coeff_C_mul,
        geometric, coeff_mk, one_pow, mul_one, pow_succ]
      ring
  apply eq_of_same_derivative_factor (W := H)
  · exact expAt_constantCoeff _ (countLog_constantCoeff _)
  · simp only [map_mul, linearFactor_const, geometric_const, mul_one]
  · unfold zetaOfCountSeries
    rw [derivative_expAt _ (countLog_constantCoeff _), hH]
  · rw [derivative_product (derivative_product (derivative_linearFactor α) (derivative_linearFactor β))
      (derivative_product (derivative_geometric (1 : K)) (derivative_geometric q))]
    unfold H
    ring

end
end ManuscriptAudit.PointCountExponential

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCountExponential.X_mul_derivative_countLog,
      ``ManuscriptAudit.PointCountExponential.eq_of_same_derivative_factor,
      ``ManuscriptAudit.PointCountExponential.geometric_eq_inv,
      ``ManuscriptAudit.PointCountExponential.twoRootCounts_zeta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
