import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Divisors

/-! Exact finite reordering of the odd-divisor part of a modulus cutoff. -/

namespace ManuscriptAudit.Paper8OddDivisorCutoff

private lemma odd_pos {g : ℕ} (hg : Odd g) : 0 < g := by
  obtain ⟨j,hj⟩ := hg
  omega

private lemma divisor_filter_eq {N k : ℕ} (hk0 : 1 ≤ k) (hkN : k ≤ N) :
    k.divisors.filter Odd = ((Finset.Icc 1 N).filter Odd).filter (fun g => g ∣ k) := by
  ext g
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hD,_⟩,hOdd⟩
    exact ⟨⟨⟨odd_pos hOdd, (Nat.le_of_dvd hk0 hD).trans hkN⟩,hOdd⟩,hD⟩
  · rintro ⟨⟨_,hOdd⟩,hD⟩
    exact ⟨⟨hD, by omega⟩,hOdd⟩

private lemma sum_divisible_indices {A : Type*} [AddCommMonoid A] (N g : ℕ) (hg : 0 < g)
    (f : ℕ → A) :
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => g ∣ k), f (k/g)) =
      ∑ j ∈ Finset.Icc 1 (N/g), f j := by
  classical
  symm
  refine Finset.sum_bij (fun j _ => g*j) ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hj0,hjN⟩ := Finset.mem_Icc.mp hj
    have hpos : 0 < g*j := Nat.mul_pos hg hj0
    have hle : g*j ≤ N := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hg).mp hjN
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos,hle⟩,⟨j,rfl⟩⟩
  · intro j _ l _ h
    exact mul_left_cancel₀ hg.ne' h
  · intro k hk
    obtain ⟨hI,⟨j,rfl⟩⟩ := Finset.mem_filter.mp hk
    obtain ⟨hj0,hjN⟩ := Finset.mem_Icc.mp hI
    have hj : 1 ≤ j := by
      by_contra! hz
      have he : j = 0 := by omega
      simp [he] at hj0
    have hj' : j ≤ N/g := (Nat.le_div_iff_mul_le hg).mpr (by simpa only [mul_comm] using hjN)
    exact ⟨j,Finset.mem_Icc.mpr ⟨hj,hj'⟩,rfl⟩
  · intro j _
    rw [Nat.mul_div_cancel_left j hg]

/-- No exchange of infinite sums is involved in this cutoff identity. -/
theorem commute_cutoff {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℕ → ℕ → A) :
    (∑ k ∈ Finset.Icc 1 N, ∑ g ∈ k.divisors.filter Odd, f g (k/g)) =
      ∑ g ∈ (Finset.Icc 1 N).filter Odd, ∑ j ∈ Finset.Icc 1 (N/g), f g j := by
  classical
  let I := Finset.Icc 1 N
  let O := I.filter Odd
  have h (k : ℕ) (hk : k ∈ I) :
      (∑ g ∈ k.divisors.filter Odd, f g (k/g)) =
        ∑ g ∈ O, if g ∣ k then f g (k/g) else 0 := by
    obtain ⟨hk0,hkN⟩ := Finset.mem_Icc.mp hk
    rw [divisor_filter_eq hk0 hkN, Finset.sum_filter]
  calc
    _ = ∑ k ∈ I, ∑ g ∈ O, if g ∣ k then f g (k/g) else 0 :=
      Finset.sum_congr rfl h
    _ = ∑ g ∈ O, ∑ k ∈ I, if g ∣ k then f g (k/g) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← Finset.sum_filter]
      exact sum_divisible_indices N g (odd_pos (Finset.mem_filter.mp hg).2) (f g)

end ManuscriptAudit.Paper8OddDivisorCutoff

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8OddDivisorCutoff.commute_cutoff
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
