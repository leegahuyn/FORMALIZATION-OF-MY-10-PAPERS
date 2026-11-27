import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicKummerHeight

/-! The symmetric pair of two polynomial coordinates has the sum of their degrees. -/

namespace ManuscriptAudit.CubicKummerSymmetricHeight

open Polynomial CubicKummerHeight

noncomputable section

/-- The symmetric product map on two homogeneous pairs. -/
def symmetric {R : Type*} [CommRing R] (a b : Fin 2 → R) : Fin 3 → R :=
  ![a 0 * b 0, a 0 * b 1 + a 1 * b 0, a 1 * b 1]

theorem map_symmetric {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : Fin 2 → R) :
    symmetric (f ∘ a) (f ∘ b) = f ∘ symmetric a b := by
  funext i
  fin_cases i <;> simp [symmetric, Function.comp_apply]

theorem symmetric_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {a b : Fin 2 → R} (ha : a ≠ 0) (hb : b ≠ 0) : symmetric a b ≠ 0 := by
  intro he
  have h₀ : a 0 * b 0 = 0 := congrFun he 0
  have h₁ : a 0 * b 1 + a 1 * b 0 = 0 := congrFun he 1
  have h₂ : a 1 * b 1 = 0 := congrFun he 2
  have hA : a 0 = 0 → a 1 ≠ 0 := by
    intro h j
    apply ha
    funext i
    fin_cases i <;> assumption
  have hB : b 0 = 0 → b 1 ≠ 0 := by
    intro h j
    apply hb
    funext i
    fin_cases i <;> assumption
  rcases mul_eq_zero.mp h₀ with h | h
  · have ha₁ := hA h
    have hb₁ := (mul_eq_zero.mp h₂).resolve_left ha₁
    have hb₀ : b 0 ≠ 0 := fun hz => hB hz hb₁
    exact mul_ne_zero ha₁ hb₀ (by simpa [h] using h₁)
  · have hb₁ := hB h
    have ha₁ := (mul_eq_zero.mp h₂).resolve_right hb₁
    have ha₀ : a 0 ≠ 0 := fun hz => hA hz ha₁
    exact mul_ne_zero ha₀ hb₁ (by simpa [h] using h₁)

variable {K : Type*} [Field K]

/-- The degree of a homogeneous polynomial pair. -/
def pairHeight (a : Fin 2 → K[X]) : ℕ := max (a 0).natDegree (a 1).natDegree

theorem natDegree_le_pairHeight (a : Fin 2 → K[X]) (i : Fin 2) :
    (a i).natDegree ≤ pairHeight a := by
  fin_cases i <;> simp [pairHeight]

theorem coeff_pairHeight_ne_zero {a : Fin 2 → K[X]} (ha : a ≠ 0) :
    (fun i => (a i).coeff (pairHeight a)) ≠ 0 := by
  intro he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  rcases le_total (a 0).natDegree (a 1).natDegree with hl | hl
  · change (a 1).coeff (max (a 0).natDegree (a 1).natDegree) = 0 at h1
    rw [max_eq_right hl, coeff_natDegree, leadingCoeff_eq_zero] at h1
    have hd : (a 0).natDegree = 0 := Nat.eq_zero_of_le_zero (by simpa [h1] using hl)
    have hH : pairHeight a = 0 := by simp [pairHeight, h1, hd]
    have h0' : a 0 = 0 := by
      change (a 0).coeff (pairHeight a) = 0 at h0
      rwa [hH, ← hd, coeff_natDegree, leadingCoeff_eq_zero] at h0
    apply ha
    funext i
    fin_cases i <;> assumption
  · change (a 0).coeff (max (a 0).natDegree (a 1).natDegree) = 0 at h0
    rw [max_eq_left hl, coeff_natDegree, leadingCoeff_eq_zero] at h0
    have hd : (a 1).natDegree = 0 := Nat.eq_zero_of_le_zero (by simpa [h0] using hl)
    have hH : pairHeight a = 0 := by simp [pairHeight, h0, hd]
    have h1' : a 1 = 0 := by
      change (a 1).coeff (pairHeight a) = 0 at h1
      rwa [hH, ← hd, coeff_natDegree, leadingCoeff_eq_zero] at h1
    apply ha
    funext i
    fin_cases i <;> assumption

/-- The symmetric product has the sum of the degrees of its polynomial factors. -/
theorem height_symmetric {a b : Fin 2 → K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    height (symmetric a b) = pairHeight a + pairHeight b := by
  let d := pairHeight a + pairHeight b
  have hm (i j : Fin 2) : (a i * b j).natDegree ≤ d :=
    natDegree_mul_le.trans <|
      Nat.add_le_add (natDegree_le_pairHeight a i) (natDegree_le_pairHeight b j)
  have hUpper : height (symmetric a b) ≤ d := by
    apply height_le
    intro i
    fin_cases i
    · exact hm 0 0
    · exact le_trans (by apply natDegree_add_le) (max_le (hm 0 1) (hm 1 0))
    · exact hm 1 1
  refine le_antisymm hUpper ?_
  have hCoeff (i j : Fin 2) :
      (a i * b j).coeff d = (a i).coeff (pairHeight a) * (b j).coeff (pairHeight b) :=
    coeff_mul_add_eq_of_natDegree_le (natDegree_le_pairHeight a i) (natDegree_le_pairHeight b j)
  have hEq : (fun i => (symmetric a b i).coeff d) =
      symmetric (fun i => (a i).coeff (pairHeight a)) (fun i => (b i).coeff (pairHeight b)) := by
    funext i
    fin_cases i <;> simp [symmetric, hCoeff]
  have hNe := symmetric_ne_zero (coeff_pairHeight_ne_zero ha) (coeff_pairHeight_ne_zero hb)
  rw [← hEq] at hNe
  by_contra! hLt
  apply hNe
  funfunext i
  exact coeff_eq_zero_of_natDegree_lt ((natDegree_le_height _ i).trans_lt hLt)

end

end ManuscriptAudit.CubicKummerSymmetricHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicKummerSymmetricHeight.map_symmetric,
      ``ManuscriptAudit.CubicKummerSymmetricHeight.symmetric_ne_zero,
      ``ManuscriptAudit.CubicKummerSymmetricHeight.coeff_pairHeight_ne_zero,
      ``ManuscriptAudit.CubicKummerSymmetricHeight.height_symmetric] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
