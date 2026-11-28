import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindKloostermanCongruence

/-! Divisor congruences and removal of the trivial three-primary additive factor. -/

namespace ManuscriptAudit.Paper8DedekindAdditiveReduction

open Paper8ContourResidueWeights Paper8DedekindKloostermanCongruence

theorem phase_numerator_congr_divisor {h k m : ℕ} (hk : 0 < k) (hC : h.Coprime k)
    (hd : m ∣ k) (a : ℤ) (ha : (h : ZMod m) * (a : ZMod m) = 1) :
    (dedekindPhaseNumerator h k : ZMod m) = (h : ZMod m) + (a : ZMod m) := by
  let H := ZMod.unitOfCoprime h hC
  let f := ZMod.castHom hd (ZMod m)
  let A := f ((H⁻¹ : (ZMod k)ˣ) : ZMod k)
  have hPos : (h : ZMod m) * A = 1 := by
    have h := congrArg f H.mul_inv
    change f ((h : ZMod k) * ((H⁻¹ : (ZMod k)ˣ) : ZMod k)) = f 1 at h
    simpa only [map_mul, map_natCast, map_one] using h
  have hA : A = (a : ZMod m) := by
    calc
      _ = (a : ZMod m) * ((h : ZMod m) * A) := by rw [← mul_assoc, mul_comm (a : ZMod m), ha, one_mul]
      _ = _ := by rw [hPos, mul_one]
  have hN := congrArg f (dedekind_phase_numerator_spec hk hC).2.1
  change f (dedekindPhaseNumerator h k : ZMod k) =
    f ((h : ZMod k) + ((H⁻¹ : (ZMod k)ˣ) : ZMod k)) at hN
  simp only [map_intCast, map_add, map_natCast] at hN
  change (dedekindPhaseNumerator h k : ZMod m) = (h : ZMod m) + A at hN
  rw [hA] at hN
  exact hN

theorem dedekind_phase_drop_three {h k : ℕ} [NeZero k] (h3 : ¬ (3 : ℕ) ∣ k) (hC : h.Coprime k)
    (u v : ℤ) (huv : 3 * u + (8 * (k : ℤ)) * v = 1) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      ZMod.stdAddChar ((u * dedekindPhaseNumerator h k : ℤ) : ZMod (8 * k)) := by
  let M := 8 * k
  let N := dedekindPhaseNumerator h k
  have hk := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  obtain ⟨a, ha⟩ := (dedekind_phase_numerator_spec hk hC).2.2.2 h3
  change N = 3 * a at ha
  have hN := congrArg (fun x : ℚ => (x : ℂ)) (dedekind_phase_numerator_spec hk hC).1
  push_cast at hN
  have hA : (a : ℂ) = 4 * (k : ℂ) * ((dedekindSum (h : ℤ) k : ℝ) : ℂ) := by
    have ha' := congrArg (fun x : ℤ => (x : ℂ)) ha
    push_cast at ha'
    change (N : ℂ) = 12 * (k : ℂ) * ((dedekindSum (h : ℤ) k : ℝ) : ℂ) at hN
    linear_combination (1 / 3 : ℂ) * hN - (1 / 3 : ℂ) * ha'
  have hUV : (3 : ZMod M) * (u : ZMod M) = 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod M)) huv
    have hM : (8 : ZMod M) * (k : ZMod M) = 0 := by
      change ((8 : ℕ) : ZMod M) * (k : ZMod M) = 0
      rw [← Nat.cast_mul, ZMod.natCast_self]
    push_cast at h
    simpa only [hM, zero_mul, add_zero] using h
  have hE : ((u * N : ℤ) : ZMod M) = (a : ZMod M) := by
    rw [ha]
    push_cast
    calc
      _ = ((3 : ZMod M) * (u : ZMod M)) * (a : ZMod M) := by ring
      _ = _ := by rw [hUV, one_mul]
  change _ = ZMod.stdAddChar ((u * N : ℤ) : ZMod M)
  rw [hE, ZMod.stdAddChar_coe]
  congr 1
  unfold M
  push_cast
  rw [hA]
  field_simp [hkC] <;> ring

end ManuscriptAudit.Paper8DedekindAdditiveReduction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DedekindAdditiveReduction.phase_numerator_congr_divisor,
      ``ManuscriptAudit.Paper8DedekindAdditiveReduction.dedekind_phase_drop_three] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
