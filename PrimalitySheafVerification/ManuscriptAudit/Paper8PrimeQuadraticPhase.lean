import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Quadratic and linear finite phases over an odd prime field, with the exact Gauss normalization. -/

namespace ManuscriptAudit.Paper8PrimeQuadraticPhase

open Finset AddChar

noncomputable section

def primeQuadraticChar (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem primeQuadraticChar_apply (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    primeQuadraticChar p t = ((quadraticChar (ZMod p) t : ℤ) : ℂ) := rfl

theorem primeQuadraticChar_sq {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    primeQuadraticChar p t ^ 2 = 1 := by
  simpa only [primeQuadraticChar_apply, Int.cast_pow, Int.cast_one] using
    congrArg (fun z : ℤ => (z : ℂ)) (quadraticChar_sq_one ht)

theorem norm_primeAdditiveChar {p : ℕ} [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (t : ZMod p) :
    ‖ψ t‖ = 1 := by
  have hchar : 0 < ringChar (ZMod p) := by
    simpa only [ZMod.ringChar_zmod_n] using (Fact.out : p.Prime).pos
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.val_mem_rootsOfUnity t hchar)
  simpa only [IsUnit.unit_spec] using h

theorem norm_primeQuadraticChar {p : ℕ} [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    ‖primeQuadraticChar p t‖ = 1 := by
  have h := congrArg norm (primeQuadraticChar_sq ht)
  rw [norm_pow, norm_one] at h
  nlinarith [norm_nonneg (primeQuadraticChar p t)]

theorem norm_gaussSum_prime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : AddChar.IsPrimitive ψ) :
    ‖gaussSum (primeQuadraticChar p) ψ‖ = Real.sqrt (p : ℝ) := by
  let χ := primeQuadraticChar p
  have hχ : χ ≠ 1 := by
    apply (MulChar.ringHomComp_ne_one_iff (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℂ))).2
    exact quadraticChar_ne_one (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hG := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq, ZMod.card] at hG
  change gaussSum χ ψ * (starRingEnd ℂ) (gaussSum χ ψ) = (p : ℂ) at hG
  rw [Complex.mul_conj'] at hG
  have hR := congrArg Complex.re hG
  have hSq : ‖gaussSum χ ψ‖ ^ 2 = (p : ℝ) := by
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.natCast_re] using hR
  rw [← hSq, Real.sqrt_sq (norm_nonneg _)]

private theorem square_fiber_card {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (y : ZMod p) :
    ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℂ) = primeQuadraticChar p y + 1 := by
  have h := quadraticChar_card_sqrts (F := ZMod p)
    (show ringChar (ZMod p) ≠ 2 by simpa only [ZMod.ringChar_zmod_n] using hp) y
  have hF : ({x : ZMod p | x ^ 2 = y} : Set (ZMod p)).toFinset = Finset.univ.filter (fun x => x ^ 2 = y) := by
    ext z
    simp
  rw [hF] at h
  have hC := congrArg (fun n : ℤ => (n : ℂ)) h
  push_cast at hC
  exact hC

theorem prime_quadratic_sum {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : AddChar.IsPrimitive ψ) {t : ZMod p} (ht : t ≠ 0) :
    (∑ x : ZMod p, ψ (t * x ^ 2)) = primeQuadraticChar p t * gaussSum (primeQuadraticChar p) ψ := by
  let χ := primeQuadraticChar p
  let e := Units.mk0 t ht
  have hZero : (∑ y : ZMod p, ψ (t * y)) = 0 := by
    simpa only [mul_comm t, if_neg ht, Nat.cast_zero] using AddChar.sum_mulShift t hψ
  have hShift : (∑ y : ZMod p, χ y * ψ (t * y)) = χ t * gaussSum χ ψ := by
    have h := gaussSum_mulShift χ ψ e
    change χ t * (∑ y : ZMod p, χ y * ψ (t * y)) = gaussSum χ ψ at h
    calc
      _ = (χ t ^ 2) * (∑ y : ZMod p, χ y * ψ (t * y)) := by rw [primeQuadraticChar_sq ht, one_mul]
      _ = _ := by rw [pow_two, mul_assoc, h]
  calc
    _ = ∑ y : ZMod p, ∑ x ∈ (Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)), ψ (t * y) :=
      (Finset.sum_fiberwise' Finset.univ (fun x : ZMod p => x ^ 2) (fun y => ψ (t * y))).symm
    _ = ∑ y : ZMod p, (χ y + 1) * ψ (t * y) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_const, nsmul_eq_mul, square_fiber_card hp y]
    _ = _ := by
      simp_rw [add_mul, one_mul]
      rw [Finset.sum_add_distrib, hZero, add_zero, hShift]

theorem prime_quadratic_linear_sum {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : AddChar.IsPrimitive ψ) {t : ZMod p} (ht : t ≠ 0) :
    (∑ x : ZMod p, ψ (t * x ^ 2 + x)) =
      ψ (-(1 : ZMod p) / (4 * t)) * primeQuadraticChar p t * gaussSum (primeQuadraticChar p) ψ := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hN : ¬ p ∣ 2 := fun h =>
      hp ((Nat.prime_two.dvd_iff_eq (Fact.out : p.Prime).ne_one).1 h).symm
    exact (not_congr (ZMod.natCast_eq_zero_iff 2 p)).2 hN
  let s : ZMod p := 1 / (2 * t)
  have hComplete (x : ZMod p) : t * x ^ 2 + x = t * (x + s) ^ 2 + (-(1 : ZMod p) / (4 * t)) := by
    unfold s
    rw [show (4 : ZMod p) = 2 * 2 by ring]
    field_simp [h2, ht] <;> ring
  have hTranslate : (∑ x : ZMod p, ψ (t * (x + s) ^ 2)) = ∑ x : ZMod p, ψ (t * x ^ 2) :=
    Fintype.sum_equiv (Equiv.addRight s) _ _ (fun _ => rfl)
  simp_rw [hComplete, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul, hTranslate, prime_quadratic_sum hp hψ ht]
  ring

end
end ManuscriptAudit.Paper8PrimeQuadraticPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8PrimeQuadraticPhase.norm_gaussSum_prime,
      ``ManuscriptAudit.Paper8PrimeQuadraticPhase.prime_quadratic_linear_sum] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
