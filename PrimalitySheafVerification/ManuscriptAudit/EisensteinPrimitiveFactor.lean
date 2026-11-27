import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusOrderValuations

/-! Extract the exact common prime-power factor of an integral coefficient pair. -/

namespace ManuscriptAudit.EisensteinPrimitiveFactor

variable (l : ℕ) [Fact l.Prime]

private theorem not_dvd_high {x : ℤ} (hx : x ≠ 0) :
    ∃ k : ℕ, ¬((l ^ k : ℕ) : ℤ) ∣ x := by
  have hAbs : x.natAbs ≠ 0 := fun h => hx (Int.natAbs_eq_zero.mp h)
  refine ⟨padicValNat l x.natAbs + 1, fun h => ?_⟩
  exact pow_succ_padicValNat_not_dvd (p := l) hAbs (Int.natCast_dvd.mp h)

/-- A pair divisible by l^n has a maximal common power at least n and a primitive quotient. -/
theorem exists_primitive_factor (a b : ℤ) (n : ℕ)
    (ha : ((l ^ n : ℕ) : ℤ) ∣ a) (hb : ((l ^ n : ℕ) : ℤ) ∣ b)
    (hNZ : a ≠ 0 ∨ b ≠ 0) :
    ∃ t u v, n ≤ t ∧ a = ((l ^ t : ℕ) : ℤ) * u ∧ b = ((l ^ t : ℕ) : ℤ) * v ∧
      ((u : ZMod l) ≠ 0 ∨ (v : ZMod l) ≠ 0) := by
  classical
  let P (k : ℕ) := ¬((l ^ k : ℕ) : ℤ) ∣ a ∨ ¬((l ^ k : ℕ) : ℤ) ∣ b
  have hEx : ∃ k, P k := by
    rcases hNZ with h | h
    · obtain ⟨k, hk⟩ := not_dvd_high l h
      exact ⟨k, Or.inl hk⟩
    · obtain ⟨k, hk⟩ := not_dvd_high l h
      exact ⟨k, Or.inr hk⟩
  let s := Nat.find hEx
  have hBad : P s := Nat.find_spec hEx
  have hs : 0 < s := by
    by_contra! h
    have hs0 : s = 0 := Nat.eq_zero_of_le_zero h
    simp [hs0, P] at hBad
  let t := s - 1
  have ht : t + 1 = s := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hs)
  have hNot : ¬P t := Nat.find_min hEx (by omega : t < s)
  have htN : n ≤ t := by
    by_contra! h
    have hsn : s ≤ n := by omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hsn
    have hDiv : ((l ^ s : ℕ) : ℤ) ∣ ((l ^ n : ℕ) : ℤ) := by
      rw [hj, pow_add, Nat.cast_mul]
      exact ⟨(l ^ j : ℕ), rfl⟩
    rcases hBad with he | he
    · exact he (hDiv.trans ha)
    · exact he (hDiv.trans hb)
  have hAd : ((l ^ t : ℕ) : ℤ) ∣ a := by
    by_contra h
    exact hNot (Or.inl h)
  have hBd : ((l ^ t : ℕ) : ℤ) ∣ b := by
    by_contra h
    exact hNot (Or.inr h)
  obtain ⟨u, hu⟩ := hAd
  obtain ⟨v, hv⟩ := hBd
  refine ⟨t, u, v, htN, hu, hv, ?_⟩
  by_contra! hBoth
  obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd u l).mp hBoth.1
  obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd v l).mp hBoth.2
  have hU : ((l ^ (t + 1) : ℕ) : ℤ) ∣ a := ⟨x, by
    rw [hu, hx, pow_succ, Nat.cast_mul, mul_assoc]⟩
  have hV : ((l ^ (t + 1) : ℕ) : ℤ) ∣ b := ⟨y, by
    rw [hv, hy, pow_succ, Nat.cast_mul, mul_assoc]⟩
  rw [ht] at hU hV
  exact hBad.elim (fun h => h hU) (fun h => h hV)

end ManuscriptAudit.EisensteinPrimitiveFactor

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EisensteinPrimitiveFactor.exists_primitive_factor
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
