import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Degree.Domain
import PrimalitySheafVerification.ManuscriptAudit.CubicKummerQuadratic

/-! Degree and absence of common roots for the centered cubic's Kummer add/sub map. -/

namespace ManuscriptAudit.CubicKummerHeight

open Polynomial CubicKummerQuadratic

variable {K : Type*} [Field K]

/-- The largest degree of the coordinates of a polynomial triple. -/
def height (v : Fin 3 → K[X]) : ℕ :=
  max (v 0).natDegree (max (v 1).natDegree (v 2).natDegree)

theorem natDegree_le_height (v : Fin 3 → K[X]) (i : Fin 3) :
    (v i).natDegree ≤ height v := by
  fin_cases i <;> simp [height, le_max_left, le_max_right]

theorem height_le {v : Fin 3 → K[X]} {n : ℕ}
    (h : ∀ i, (v i).natDegree ≤ n) : height v ≤ n :=
  max_le (h 0) (max_le (h 1) (h 2))

private theorem attained (v : Fin 3 → K[X]) :
    ∃ i, (v i).natDegree = height v := by
  rcases le_total (v 0).natDegree (max (v 1).natDegree (v 2).natDegree) with h | h
  · rcases le_total (v 1).natDegree (v 2).natDegree with h' | h'
    · exact ⟨2, by rw [height, max_eq_right h, max_eq_right h']⟩
    · exact ⟨1, by rw [height, max_eq_right h, max_eq_left h']⟩
  · exact ⟨0, by rw [height, max_eq_left h]⟩

/-- The leading-coefficient vector at the maximal degree is nonzero. -/
theorem coeff_height_ne_zero {v : Fin 3 → K[X]} (hv : v ≠ 0) :
    (fun i => (v i).coeff (height v)) ≠ 0 := by
  intro he
  obtain ⟨i, hi⟩ := attained v
  have h0 : (v i).leadingCoeff = 0 := by
    rw [← coeff_natDegree, hi]
    exact congrFun he i
  have hz := leadingCoeff_eq_zero.mp h0
  have hh : height v = 0 := by simp [← hi, hz]
  apply hv
  funext j
  change v j = 0
  have hj : (v j).natDegree = 0 := Nat.eq_zero_of_le_zero (hh ▸ natDegree_le_height v j)
  apply leadingCoeff_eq_zero.mp
  rw [← coeff_natDegree, hj, ← hh]
  exact congrFun he j

private theorem coefficient_forms {v : Fin 3 → K[X]} (A : K) {n : ℕ}
    (h : ∀ i, (v i).natDegree ≤ n) :
    (fun i => ((forms (C A) v) i).coeff (n + n)) =
      forms A (fun i => (v i).coeff n) := by
  have hTwo : (2 : K[X]) = C (2 : K) := by rw [map_ofNat]
  have h₄ : (4 : K[X]) = C (4 : K) := by rw [map_ofNat]
  have hFour : (4 : K[X]) * C A = C (4 * A) := by rw [h₄, map_mul]
  funext i
  have hM (i j : Fin 3) : (v i * v j).coeff (n + n) = (v i).coeff n * (v j).coeff n :=
    coeff_mul_add_eq_of_natDegree_le (h i) (h j)
  fin_cases i
  · change ((v 0) ^ 2 - (4 * C A) * (v 1 * v 2)).coeff (n + n) =
      (v 0).coeff n ^ 2 - (4 * A) * ((v 1).coeff n * (v 2).coeff n)
    rw [hFour, coeff_sub, pow_two, coeff_C_mul, hM, hM, pow_two]
  · change (2 * (v 1 * v 0) + (4 * C A) * (v 2 * v 2)).coeff (n + n) =
      2 * ((v 1).coeff n * (v 0).coeff n) + (4 * A) * ((v 2).coeff n * (v 2).coeff n)
    rw [hTwo, hFour, coeff_add, coeff_C_mul, coeff_C_mul, hM, hM]
  · change ((v 1) ^ 2 - 4 * (v 0 * v 2)).coeff (n + n) =
      (v 1).coeff n ^ 2 - 4 * ((v 0).coeff n * (v 2).coeff n)
    rw [h₄, coeff_sub, pow_two, coeff_C_mul, hM, hM, pow_two]

private theorem height_forms_le {v : Fin 3 → K[X]} (A : K) :
    height (forms (C A) v) ≤ height v + height v := by
  let n := height v
  have hMul (i j : Fin 3) : (v i * v j).natDegree ≤ n + n :=
    natDegree_mul_le.trans (Nat.add_le_add (natDegree_le_height v i) (natDegree_le_height v j))
  have hTwo : (2 : K[X]) = C (2 : K) := by rw [map_ofNat]
  have h₄ : (4 : K[X]) = C (4 : K) := by rw [map_ofNat]
  have hFour : (4 : K[X]) * C A = C (4 * A) := by rw [h₄, map_mul]
  apply height_le
  intro i
  fin_cases i
  · simp only [forms, Matrix.cons_val_zero, pow_two, hFour]
    exact le_trans (by apply natDegree_sub_le) (max_le (hMul 0 0)
      ((natDegree_C_mul_le _ _).trans (hMul 1 2)))
  · simp only [forms, Matrix.cons_val_one, Matrix.cons_val_zero, pow_two, hFour, hTwo]
    exact le_trans (by apply natDegree_add_le) (max_le ((natDegree_C_mul_le _ _).trans (hMul 1 0))
      ((natDegree_C_mul_le _ _).trans (hMul 2 2)))
  · change ((v 1) ^ 2 - 4 * (v 0 * v 2)).natDegree ≤ n + n
    rw [pow_two, h₄]
    exact le_trans (by apply natDegree_sub_le) (max_le (hMul 1 1)
      ((natDegree_C_mul_le _ _).trans (hMul 0 2)))

/-- A nonzero polynomial triple doubles its degree in the native homogeneous add/sub map. -/
theorem height_forms (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) {A : K}
    (hA : A ≠ 0) {v : Fin 3 → K[X]} (hv : v ≠ 0) :
    height (forms (C A) v) = height v + height v := by
  refine le_antisymm (height_forms_le A) ?_
  have hTop := coefficient_forms A (natDegree_le_height v)
  have hNe := forms_ne_zero h₂ h₃ hA (coeff_height_ne_zero hv)
  rw [← hTop] at hNe
  by_contra! hLower
  apply hNe
  funext i
  exact coeff_eq_zero_of_natDegree_lt ((natDegree_le_height _ i).trans_lt hLower)

/-- The add/sub map preserves the absence of common zeroes after extension of scalars. -/
theorem no_common_root_forms {L : Type*} [Field L] [Algebra K L]
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) {A : K} (hA : A ≠ 0)
    {v : Fin 3 → K[X]} {x : L} (hv : (fun i => (v i).eval₂ (algebraMap K L) x) ≠ 0) :
    (fun i => (forms (C A) v i).eval₂ (algebraMap K L) x) ≠ 0 := by
  let e := Polynomial.eval₂RingHom (algebraMap K L) x
  have hEq := map_forms e (C A) v
  have heA : e (C A) = algebraMap K L A := by simp [e]
  rw [heA] at hEq
  change forms (algebraMap K L A) (fun i => (v i).eval₂ (algebraMap K L) x) =
    (fun i => (forms (C A) v i).eval₂ (algebraMap K L) x) at hEq
  rw [← hEq]
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  exact forms_ne_zero h₂' h₃' ((map_ne_zero (algebraMap K L)).mpr hA) hv

end ManuscriptAudit.CubicKummerHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicKummerHeight.natDegree_le_height,
      ``ManuscriptAudit.CubicKummerHeight.height_le,
      ``ManuscriptAudit.CubicKummerHeight.coeff_height_ne_zero,
      ``ManuscriptAudit.CubicKummerHeight.height_forms,
      ``ManuscriptAudit.CubicKummerHeight.no_common_root_forms] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
