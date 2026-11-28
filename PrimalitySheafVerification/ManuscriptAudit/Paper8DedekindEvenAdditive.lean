import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenPhaseSign

/-! The exact two-adic additive phase splits into a fixed phase, a Jacobi sign, and a Kloosterman term. -/

namespace ManuscriptAudit.Paper8DedekindEvenAdditive

open Paper8DedekindEvenPhaseSign Paper8DedekindKloostermanCongruence

noncomputable section

private theorem stdAddChar_half_eight_mul {t : ℕ} [NeZero t] :
    ZMod.stdAddChar ((4 * (t : ℤ) : ℤ) : ZMod (8 * t)) = -1 := by
  rw [ZMod.stdAddChar_coe, ← Complex.exp_pi_mul_I]
  congr 1
  have hT : (t : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne t)
  push_cast
  field_simp [hT] <;> ring

private theorem stdAddChar_four_mul_odd {t n k : ℕ} [NeZero t]
    (hK : k = t * n) (hn : n % 2 = 1) (v : ℤ) (hv : (2 : ℤ) ∣ v - 1) :
    ZMod.stdAddChar ((4 : ZMod (8 * t)) * (k : ZMod (8 * t)) * (v : ZMod (8 * t))) = -1 := by
  have hn2 : (n : ZMod 2) = 1 := by
    change (n : ZMod 2) = ((1 : ℕ) : ZMod 2)
    exact (ZMod.natCast_eq_natCast_iff' n 1 2).2 (by simpa using hn)
  have hv2 : (v : ZMod 2) = 1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (v - 1) 2).2 hv
    push_cast at h
    exact sub_eq_zero.mp h
  have hNv : (2 : ℤ) ∣ (n : ℤ) * v - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
    push_cast
    rw [hn2, hv2, one_mul, sub_self]
  obtain ⟨q, hq⟩ := hNv
  have hKC := congrArg (fun x : ℕ => (x : ℤ)) hK
  push_cast at hKC
  have hD : ((8 * t : ℕ) : ℤ) ∣ 4 * (k : ℤ) * v - 4 * (t : ℤ) := by
    refine ⟨q, ?_⟩
    push_cast
    linear_combination 4 * v * hKC + 4 * (t : ℤ) * hq
  have hZ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (8 * t)).2 hD
  push_cast at hZ
  have hE := sub_eq_zero.mp hZ
  rw [hE]
  simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using stdAddChar_half_eight_mul (t := t)

theorem stdAddChar_even_phase_factor {h k t n : ℕ} [NeZero t]
    (hh : h % 2 = 1) (hk : k % 2 = 0) (hk0 : 0 < k) (hC : h.Coprime k)
    (hK : k = t * n) (hn : n % 2 = 1) (a v : ℤ) (hv : (2 : ℤ) ∣ v - 1)
    (ha : (h : ZMod (8 * t)) * (a : ZMod (8 * t)) = 1) :
    ZMod.stdAddChar ((v : ZMod (8 * t)) * (dedekindPhaseNumerator h k : ZMod (8 * t))) =
      ZMod.stdAddChar (-(2 : ZMod (8 * t)) * (k : ZMod (8 * t)) * (v : ZMod (8 * t))) *
        (jacobiSym (-(k : ℤ)) h : ℂ) *
        ZMod.stdAddChar ((v : ZMod (8 * t)) * ((1 - (k : ZMod (8 * t))) * (h : ZMod (8 * t)) +
          ((k : ZMod (8 * t)) ^ 2 + 1) * (a : ZMod (8 * t)))) := by
  let M := 8 * t
  let J := jacobiSym (-(k : ℤ)) h
  let A : ZMod M := (1 - (k : ZMod M)) * (h : ZMod M) + ((k : ZMod M) ^ 2 + 1) * (a : ZMod M)
  let B : ZMod M := -(2 : ZMod M) * (k : ZMod M) * (v : ZMod M)
  have hJ : J = 1 ∨ J = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    simp only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact hC.symm.gcd_eq_one
  have hB : ZMod.stdAddChar (B * (J : ZMod M)) = ZMod.stdAddChar B * (J : ℂ) := by
    rcases hJ with hS | hS
    · rw [hS, Int.cast_one, Int.cast_one, mul_one, mul_one]
    · rw [hS]
      have hArg : B * ((-1 : ℤ) : ZMod M) =
          B + (4 : ZMod M) * (k : ZMod M) * (v : ZMod M) := by
        unfold B
        push_cast
        ring
      rw [hArg, AddChar.map_add_eq_mul, stdAddChar_four_mul_odd hK hn v hv]
      push_cast
      ring
  have hN := phase_even_numerator_two_part_signed hh hk hk0 hC (show t ∣ k from ⟨n, hK⟩) a ha
  change (dedekindPhaseNumerator h k : ZMod M) = A - 2 * (k : ZMod M) * (J : ZMod M) at hN
  change ZMod.stdAddChar ((v : ZMod M) * (dedekindPhaseNumerator h k : ZMod M)) =
    ZMod.stdAddChar B * (J : ℂ) * ZMod.stdAddChar ((v : ZMod M) * A)
  have hArg : (v : ZMod M) * (A - 2 * (k : ZMod M) * (J : ZMod M)) =
      B * (J : ZMod M) + (v : ZMod M) * A := by
    unfold B
    ring
  rw [hN, hArg, AddChar.map_add_eq_mul, hB]

end
end ManuscriptAudit.Paper8DedekindEvenAdditive

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenAdditive.stdAddChar_even_phase_factor
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
