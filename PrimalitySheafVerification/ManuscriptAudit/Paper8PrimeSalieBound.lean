import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimeQuadraticPhase

/-! Exact finite Salié decomposition and square-root bound over every odd prime field. -/

namespace ManuscriptAudit.Paper8PrimeSalieBound

open Finset AddChar Paper8PrimeQuadraticPhase

noncomputable section

def primeSalieSum {p : ℕ} [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (a b : ZMod p) : ℂ :=
  ∑ d : ZMod p, primeQuadraticChar p d * ψ (a * d + b / d)

def primeSalieRootSum {p : ℕ} [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (a b : ZMod p) : ℂ :=
  ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 4 * a * b)), ψ x

theorem primeSalie_root_identity {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : AddChar.IsPrimitive ψ) (a : ZMod p) {b : ZMod p} (hb : b ≠ 0) :
    (p : ℂ) * primeSalieRootSum ψ a b =
      gaussSum (primeQuadraticChar p) ψ * primeQuadraticChar p (-(4 : ZMod p) * b) * primeSalieSum ψ a b := by
  let χ := primeQuadraticChar p
  let G := gaussSum χ ψ
  let β := 4 * a * b
  let c := -(4 : ZMod p) * b
  let S (d : ZMod p) := χ d * ψ (a * d + b / d)
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hN : ¬ p ∣ 2 := fun h =>
      hp ((Nat.prime_two.dvd_iff_eq (Fact.out : p.Prime).ne_one).1 h).symm
    exact (not_congr (ZMod.natCast_eq_zero_iff 2 p)).2 hN
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by ring]
    exact mul_ne_zero h2 h2
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h4) hb
  have hZero : (∑ x : ZMod p, ψ x) = 0 := by
    simpa only [mul_one, if_neg one_ne_zero] using AddChar.sum_mulShift (1 : ZMod p) hψ
  have hCharZero : χ 0 = 0 := by simp [χ, primeQuadraticChar_apply]
  have hRoot :
      (∑ t : ZMod p, ∑ x : ZMod p, ψ (t * (x ^ 2 - β)) * ψ x) =
        (p : ℂ) * primeSalieRootSum ψ a b := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, mul_comm _ (_ - β)]
    simp_rw [AddChar.sum_mulShift _ hψ, sub_eq_zero, ZMod.card, ite_mul, zero_mul]
    unfold primeSalieRootSum
    rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp)
  have hArrange (t x : ZMod p) :
      ψ (t * (x ^ 2 - β)) * ψ x = ψ (-(β * t)) * ψ (t * x ^ 2 + x) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hEval (t : ZMod p) :
      ψ (-(β * t)) * (∑ x : ZMod p, ψ (t * x ^ 2 + x)) = (G * χ c) * S (c * t) := by
    by_cases ht : t = 0
    · subst t
      simp [hZero, S, hCharZero]
    · have hX := prime_quadratic_linear_sum hp hψ ht
      change (∑ x : ZMod p, ψ (t * x ^ 2 + x)) = ψ (-(1 : ZMod p) / (4 * t)) * χ t * G at hX
      have hPhase : -(β * t) + (-(1 : ZMod p) / (4 * t)) = a * (c * t) + b / (c * t) := by
        unfold β c
        field_simp [h4, hb, ht] <;> ring
      have hχ : χ t = χ c * χ (c * t) := by
        rw [map_mul, ← mul_assoc, ← pow_two, primeQuadraticChar_sq hc, one_mul]
      rw [hX, hχ]
      unfold S
      calc
        _ = G * χ c * χ (c * t) * (ψ (-(β * t)) * ψ (-(1 : ZMod p) / (4 * t))) := by ring
        _ = _ := by rw [← AddChar.map_add_eq_mul, hPhase]; ring
  have hReindex : (∑ t : ZMod p, S (c * t)) = ∑ d : ZMod p, S d :=
    Fintype.sum_bijective _ (Units.mk0 c hc).mulLeft_bijective _ _ (fun _ => rfl)
  calc
    _ = ∑ t : ZMod p, ∑ x : ZMod p, ψ (t * (x ^ 2 - β)) * ψ x := hRoot.symm
    _ = ∑ t : ZMod p, ψ (-(β * t)) * ∑ x : ZMod p, ψ (t * x ^ 2 + x) := by
      simp_rw [hArrange, ← Finset.mul_sum]
    _ = _ := by
      simp_rw [hEval, ← Finset.mul_sum, hReindex] <;> rfl

theorem norm_primeSalieRootSum_le {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (ψ : AddChar (ZMod p) ℂ) (a b : ZMod p) : ‖primeSalieRootSum ψ a b‖ ≤ 2 := by
  let β := 4 * a * b
  let R := Finset.univ.filter (fun x : ZMod p => x ^ 2 = β)
  have hCard := quadraticChar_card_sqrts (F := ZMod p)
    (by simpa only [ZMod.ringChar_zmod_n] using hp) β
  have hR : ({x : ZMod p | x ^ 2 = β} : Set (ZMod p)).toFinset = R := by
    ext x
    simp [R]
  rw [hR] at hCard
  have hχ : quadraticChar (ZMod p) β ≤ 1 := by
    by_cases h : β = 0
    · simp [h]
    · rcases quadraticChar_dichotomy h with h | h <;> rw [h] <;> norm_num
  have hc : R.card ≤ 2 := by
    have hc' : (R.card : ℤ) ≤ 2 := by rw [hCard]; linarith
    exact_mod_cast hc'
  change ‖∑ x ∈ R, ψ x‖ ≤ 2
  refine (norm_sum_le R _).trans ?_
  simp only [norm_primeAdditiveChar, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast hc

theorem norm_primeSalieSum_le {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : AddChar.IsPrimitive ψ) (a : ZMod p) {b : ZMod p} (hb : b ≠ 0) :
    ‖primeSalieSum ψ a b‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hN : ¬ p ∣ 2 := fun h =>
      hp ((Nat.prime_two.dvd_iff_eq (Fact.out : p.Prime).ne_one).1 h).symm
    exact (not_congr (ZMod.natCast_eq_zero_iff 2 p)).2 hN
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by ring]
    exact mul_ne_zero h2 h2
  have hc : (-(4 : ZMod p) * b) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h4) hb
  have h := congrArg norm (primeSalie_root_identity hp hψ a hb)
  simp only [norm_mul, Complex.norm_natCast, norm_gaussSum_prime hp hψ, norm_primeQuadraticChar hc, mul_one] at h
  have hEq : ‖primeSalieSum ψ a b‖ = Real.sqrt (p : ℝ) * ‖primeSalieRootSum ψ a b‖ := by
    apply mul_left_cancel₀ (Real.sqrt_pos.2 hp0).ne'
    calc
      _ = (p : ℝ) * ‖primeSalieRootSum ψ a b‖ := h.symm
      _ = _ := by rw [← mul_assoc, ← pow_two, Real.sq_sqrt hp0.le]
  rw [hEq, mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (norm_primeSalieRootSum_le hp ψ a b) (Real.sqrt_nonneg _)

end
end ManuscriptAudit.Paper8PrimeSalieBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8PrimeSalieBound.norm_primeSalieSum_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
