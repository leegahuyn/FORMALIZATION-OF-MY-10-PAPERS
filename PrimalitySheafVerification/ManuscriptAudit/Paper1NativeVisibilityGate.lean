import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Sqrt
import Mathlib.RingTheory.Localization.AtPrime.Basic
import PrimalitySheafVerification.ManuscriptAudit.IntPrimeResidueFiber

/-! The literal finite trial-divisor gate using the actual local rings on Spec ℤ. -/

namespace ManuscriptAudit.Paper1NativeVisibilityGate

open IntPrimeResidueFiber

local instance closedPoint_isPrime (p : ℕ) [Fact p.Prime] :
    (closedPoint p).asIdeal.IsPrime := (closedPoint p : PrimeSpectrum ℤ).isPrime

/-- At every visible prime point up to the integer square root, X must be a local unit. -/
def passes (U : Set (PrimeSpectrum ℤ)) (X : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], closedPoint p ∈ U → p ≤ X.sqrt →
    IsUnit (algebraMap ℤ (Localization.AtPrime (closedPoint p).asIdeal) (X : ℤ))

theorem local_unit_iff_not_dvd (p X : ℕ) [Fact p.Prime] :
    IsUnit (algebraMap ℤ (Localization.AtPrime (closedPoint p).asIdeal) (X : ℤ)) ↔
      ¬ p ∣ X := by
  let I := (closedPoint p).asIdeal
  letI : I.IsPrime := (closedPoint p).isPrime
  change IsUnit (algebraMap ℤ (Localization.AtPrime I) (X : ℤ)) ↔ ¬ p ∣ X
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime I) I]
  change ((X : ℤ) ∉ (closedPoint p).asIdeal) ↔ ¬ p ∣ X
  rw [closedPoint_ideal p, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

private theorem small_prime_divisor (X : ℕ) (hX : 2 ≤ X) (hn : ¬ X.Prime) :
    ∃ p, p.Prime ∧ p ≤ X.sqrt ∧ p ∣ X := by
  obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hX).mp hn
  have hFactor : ∃ d, d ≤ X.sqrt ∧ d ≠ 1 ∧ d ∣ X := by
    rcases Nat.le_sqrt_of_eq_mul hab.symm with hal | hbl
    · refine ⟨a, hal, ?_, ⟨b, hab.symm⟩⟩
      intro he
      rw [he, one_mul] at hab
      omega
    · refine ⟨b, hbl, ?_, ⟨a, by rw [mul_comm]; exact hab.symm⟩⟩
      intro he
      rw [he, mul_one] at hab
      omega
  obtain ⟨d, hds, hd1, hdX⟩ := hFactor
  have hdPos : 0 < d := by
    by_contra! h
    have he : d = 0 := by omega
    rw [he, zero_dvd_iff] at hdX
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  exact ⟨p, hp, (Nat.le_of_dvd hdPos hpd).trans hds, hpd.trans hdX⟩

theorem prime_passes {U : Set (PrimeSpectrum ℤ)} {X : ℕ} (hX : X.Prime) :
    passes U X := by
  intro p hP _ hSmall
  apply (local_unit_iff_not_dvd p X).2
  intro hd
  have hp : p.Prime := hP.out
  have he := (Nat.dvd_prime_two_le hX hp.two_le).mp hd
  subst X
  have hSq := Nat.le_sqrt.mp hSmall
  have hlt : p < p*p := by
    calc
      p = p*1 := (mul_one _).symm
      _ < p*p := mul_lt_mul_of_pos_left (Nat.lt_of_succ_le hp.two_le) hp.pos
  exact (not_le_of_gt hlt) hSq

theorem omitted_prime_square_passes {U : Set (PrimeSpectrum ℤ)} (p : ℕ) [Fact p.Prime]
    (hmiss : closedPoint p ∉ U) : passes U (p^2) ∧ ¬ (p^2).Prime := by
  have hp : p.Prime := Fact.out
  constructor
  · intro q hQ hvis _
    apply (local_unit_iff_not_dvd q (p^2)).2
    intro hd
    have hqp := (Nat.prime_dvd_prime_iff_eq hQ.out hp).mp (hQ.out.dvd_of_dvd_pow hd)
    subst q
    exact hmiss hvis
  · intro h
    rw [pow_two, Nat.prime_mul_iff] at h
    have h2 := hp.two_le
    rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem global_correctness_iff_full_visibility (U : Set (PrimeSpectrum ℤ)) :
    (∀ X : ℕ, 2 ≤ X → (passes U X ↔ X.Prime)) ↔
      (∀ (p : ℕ) [Fact p.Prime], closedPoint p ∈ U) := by
  constructor
  · intro h p hP
    by_contra hmiss
    obtain ⟨hgate, hnot⟩ := omitted_prime_square_passes p hmiss
    have hp : p.Prime := hP.out
    have hp2 : 2 ≤ p^2 := by nlinarith [hp.two_le]
    exact hnot ((h (p^2) hp2).1 hgate)
  · intro h X hX
    refine ⟨?_, prime_passes⟩
    intro hgate
    by_contra hn
    obtain ⟨p, hp, hsmall, hdvd⟩ := small_prime_divisor X hX hn
    letI : Fact p.Prime := ⟨hp⟩
    exact (local_unit_iff_not_dvd p X).1 (hgate p (h p) hsmall) hdvd

theorem omitted_D_prime_square_passes (f : ℤ) (p : ℕ) [Fact p.Prime]
    (hdiv : (p : ℤ) ∣ f) :
    passes (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum ℤ)) (p^2) ∧ ¬ (p^2).Prime := by
  apply omitted_prime_square_passes p
  intro h
  change f ∉ (closedPoint p).asIdeal at h
  apply h
  rwa [closedPoint_ideal p, Ideal.mem_span_singleton]

end ManuscriptAudit.Paper1NativeVisibilityGate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper1NativeVisibilityGate.local_unit_iff_not_dvd,
      ``ManuscriptAudit.Paper1NativeVisibilityGate.prime_passes,
      ``ManuscriptAudit.Paper1NativeVisibilityGate.omitted_prime_square_passes,
      ``ManuscriptAudit.Paper1NativeVisibilityGate.global_correctness_iff_full_visibility,
      ``ManuscriptAudit.Paper1NativeVisibilityGate.omitted_D_prime_square_passes] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
