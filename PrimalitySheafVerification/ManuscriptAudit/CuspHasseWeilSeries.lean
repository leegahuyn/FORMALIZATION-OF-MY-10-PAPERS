import Lean.Util.CollectAxioms
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CuspPointCountSeries

/-!
# Hasse–Weil series determined by the actual cusp point counts

The exponential zeta series is formed from the actual point counts over
every positive-degree finite-field extension. Formal differentiation
over ℚ gives the affine cusp factor and the factor for the puncture.
-/

namespace ManuscriptAudit.CuspHasseWeilSeries

open PowerSeries CuspPointCountSeries

noncomputable section

private abbrev Series := ℚ⟦X⟧

private def countLog (counts : Series) : Series :=
  PowerSeries.mk fun n => if n = 0 then 0 else coeff n counts / (n : ℚ)

private def expAt (f : Series) : Series :=
  (PowerSeries.exp ℚ).subst f

/-- The exponential zeta series obtained from the positive-degree point counts. -/
def zetaOfCountSeries (counts : Series) : Series :=
  expAt (countLog counts)

private theorem countLog_constantCoeff (counts : Series) :
    constantCoeff (countLog counts) = 0 := by
  simp [countLog, constantCoeff_mk]

private theorem X_mul_derivative_countLog (counts : Series) (hc : constantCoeff counts = 0) :
    X * derivative ℚ (countLog counts) = counts := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, hc]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, countLog, coeff_mk, if_neg n.succ_ne_zero]
    simp only [Nat.cast_add, Nat.cast_one]
    exact div_mul_cancel₀ _ (by positivity : (n : ℚ) + 1 ≠ 0)

private theorem expAt_constantCoeff (f : Series) (hf : constantCoeff f = 0) :
    constantCoeff (expAt f) = 1 := by
  have hSubst : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  have hOther (j : ℕ) (hj : j ≠ 0) :
      coeff j (PowerSeries.exp ℚ) • coeff 0 (f ^ j) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hf, zero_pow hj, smul_zero]
  change constantCoeff ((PowerSeries.exp ℚ).subst f) = 1
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hSubst, finsum_eq_single _ 0 hOther] <;>
    simp [coeff_zero_eq_constantCoeff_apply]

private theorem derivative_expAt (f : Series) (hf : constantCoeff f = 0) :
    derivative ℚ (expAt f) = expAt f * derivative ℚ f := by
  have hSubst : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  unfold expAt
  first
  | rw [derivative_subst ℚ hSubst, derivative_exp ℚ]
  | rw [derivative_subst hSubst, derivative_exp ℚ]

private theorem derivative_one : derivative ℚ (1 : Series) = 0 :=
  PowerSeries.derivativeFun_one

private theorem eq_of_same_derivative_factor {F G W : Series}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    (dF : derivative ℚ F = F * W) (dG : derivative ℚ G = G * W) :
    F = G := by
  have hn : constantCoeff G ≠ 0 := by
    rw [hG]
    exact one_ne_zero
  have hInv := PowerSeries.mul_inv_cancel G hn
  have hD : derivative ℚ (F * G⁻¹) = derivative ℚ (1 : Series) := by
    rw [derivative_one, Derivation.leibniz, derivative_inv', dF, dG]
    simp only [smul_eq_mul]
    linear_combination -(F * G⁻¹ * W) * hInv
  have hC : constantCoeff (F * G⁻¹) = constantCoeff (1 : Series) := by
    simp only [map_mul, constantCoeff_inv, hF, hG, inv_one, mul_one, map_one]
  have h := PowerSeries.derivative.ext hD hC
  calc
    F = F * (G⁻¹ * G) := by rw [PowerSeries.inv_mul_cancel G hn, mul_one]
    _ = (F * G⁻¹) * G := by rw [mul_assoc]
    _ = G := by rw [h, one_mul]

private theorem geometric_constantCoeff (q : ℚ) : constantCoeff (geometric q) = 1 := by
  simp [geometric, constantCoeff_mk]

private theorem geometric_eq_inv (q : ℚ) : geometric q = (1 - (X : Series) * C q)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one (by simp : constantCoeff (1 - (X : Series) * C q) ≠ 0)).2
  simpa only [mul_comm] using one_sub_mul_geometric q

private theorem derivative_denominator (q : ℚ) :
    derivative ℚ (1 - (X : Series) * C q) = -C q := by
  rw [map_sub, derivative_one, Derivation.leibniz]
  simp [smul_eq_mul]

private theorem derivative_geometric (q : ℚ) :
    derivative ℚ (geometric q) = geometric q * (C q * geometric q) := by
  rw [geometric_eq_inv q, derivative_inv', derivative_denominator]
  ring

/-- The exponential zeta series of the actual affine cusp field-point counts. -/
def cuspZeta (p : ℕ) [Fact p.Prime] : Series :=
  expAt (countLog (cuspSeries p))

/-- The exponential zeta series of the punctured cusp field-point counts. -/
def punctureZeta (p : ℕ) [Fact p.Prime] : Series :=
  expAt (countLog (punctureSeries p))

private theorem derivative_cusp_countLog (p : ℕ) [Fact p.Prime] :
    derivative ℚ (countLog (cuspSeries p)) = C (p : ℚ) * geometric (p : ℚ) := by
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero : (X : Series) ≠ 0)
  exact (X_mul_derivative_countLog (cuspSeries p) (by simp [cuspSeries])).trans (cuspSeries_eq p)

private theorem derivative_puncture_countLog (p : ℕ) [Fact p.Prime] :
    derivative ℚ (countLog (punctureSeries p)) = C (p : ℚ) * geometric (p : ℚ) - geometric 1 := by
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero : (X : Series) ≠ 0)
  calc
    _ = punctureSeries p := X_mul_derivative_countLog (punctureSeries p) (by simp [punctureSeries])
    _ = cuspSeries p - (cuspSeries p - punctureSeries p) := by ring
    _ = X * (C (p : ℚ) * geometric (p : ℚ) - geometric 1) := by
      rw [cuspSeries_sub_punctureSeries p, cuspSeries_eq p, mul_sub]

private theorem cuspZeta_eq_geometric (p : ℕ) [Fact p.Prime] :
    cuspZeta p = geometric (p : ℚ) := by
  apply eq_of_same_derivative_factor (W := C (p : ℚ) * geometric (p : ℚ))
  · exact expAt_constantCoeff _ (countLog_constantCoeff _)
  · exact geometric_constantCoeff _
  · unfold cuspZeta
    rw [derivative_expAt _ (countLog_constantCoeff _), derivative_cusp_countLog p]
  · exact derivative_geometric _

/-- The affine cusp factor is `1 / (1 − pX)` over the formal power series ring. -/
theorem cuspZeta_eq_inv (p : ℕ) [Fact p.Prime] :
    cuspZeta p = (1 - (X : Series) * C (p : ℚ))⁻¹ :=
  (cuspZeta_eq_geometric p).trans (geometric_eq_inv _)

/-- Removing the rational origin multiplies the exponential zeta series by `1 − X`. -/
theorem punctureZeta_eq_mul_cuspZeta (p : ℕ) [Fact p.Prime] :
    punctureZeta p = (1 - (X : Series)) * cuspZeta p := by
  rw [cuspZeta_eq_geometric p]
  apply eq_of_same_derivative_factor (W := C (p : ℚ) * geometric (p : ℚ) - geometric 1)
  · exact expAt_constantCoeff _ (countLog_constantCoeff _)
  · simp [geometric_constantCoeff]
  · unfold punctureZeta
    rw [derivative_expAt _ (countLog_constantCoeff _), derivative_puncture_countLog p]
  · have h : (1 - (X : Series)) * geometric 1 = 1 := by
      simpa using one_sub_mul_geometric 1
    have hD : derivative ℚ (1 - (X : Series)) = -1 := by
      simpa using derivative_denominator 1
    rw [Derivation.leibniz, hD, derivative_geometric]
    simp only [smul_eq_mul]
    linear_combination geometric (p : ℚ) * h

/-- The puncture's formal Hasse–Weil factor is `(1 − X) / (1 − pX)`. -/
theorem punctureZeta_eq_mul_inv (p : ℕ) [Fact p.Prime] :
    punctureZeta p = (1 - (X : Series)) * (1 - (X : Series) * C (p : ℚ))⁻¹ := by
  rw [punctureZeta_eq_mul_cuspZeta p, cuspZeta_eq_inv p]

end

end ManuscriptAudit.CuspHasseWeilSeries

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspHasseWeilSeries.cuspZeta_eq_inv,
      ``ManuscriptAudit.CuspHasseWeilSeries.punctureZeta_eq_mul_cuspZeta,
      ``ManuscriptAudit.CuspHasseWeilSeries.punctureZeta_eq_mul_inv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
