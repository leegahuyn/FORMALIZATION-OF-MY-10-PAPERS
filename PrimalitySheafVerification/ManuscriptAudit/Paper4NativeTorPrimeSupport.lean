import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntCyclicDerivedTorGcd
import PrimalitySheafVerification.ManuscriptAudit.Paper4ExceptionalPrimeProgression

/-! Paper 4, physical pp. 104–106 and 139–140: the prime support of the
actual degree-one Tor detector and the accompanying divisibility support. -/

namespace ManuscriptAudit.Paper4NativeTorPrimeSupport

open CategoryTheory CategoryTheory.Limits

noncomputable section

private abbrev C := ModuleCat.{0} ℤ

/-- The actual obstruction object, using the integer residue modules. -/
abbrev obstruction (m p k : ℕ) : C :=
  ((Tor C 1).obj (ModuleCat.of ℤ (ZMod m))).obj (ModuleCat.of ℤ (ZMod (p ^ k)))

theorem obstruction_isZero_iff {m p k : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hk : 0 < k) : IsZero (obstruction m p k) ↔ ¬ p ∣ m := by
  let g := Nat.gcd m (p ^ k)
  letI : NeZero g := ⟨(Nat.gcd_pos_of_pos_left (p ^ k) hm).ne'⟩
  have hCard : Nat.card (ZMod g) = g := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hRes : Subsingleton (ZMod g) ↔ g = 1 := by
    constructor
    · intro h
      exact hCard.symm.trans (Nat.card_eq_one_iff_unique.mpr ⟨h, ⟨0⟩⟩)
    · intro h
      exact (Nat.card_eq_one_iff_unique.mp (hCard.trans h)).1
  calc
    IsZero (obstruction m p k) ↔ IsZero (ModuleCat.of ℤ (ZMod g)) :=
      (IntCyclicDerivedTorGcd.torOneIsoGcdResidues m (p ^ k) hm (pow_pos hp.pos k)).isZero_iff
    _ ↔ Subsingleton (ZMod g) := ModuleCat.isZero_iff_subsingleton
    _ ↔ m.Coprime (p ^ k) := hRes
    _ ↔ ¬ p ∣ m := by
      rw [Nat.coprime_pow_right_iff hk, Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd

/-- The set of actual nonzero degree-one obstructions is the finite prime factor set. -/
theorem tor_prime_support {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    {p : ℕ | p.Prime ∧ ¬ IsZero (obstruction m p k)} = (m.primeFactors : Set ℕ) := by
  classical
  ext p
  change (p.Prime ∧ ¬ IsZero (obstruction m p k)) ↔ p ∈ m.primeFactors
  by_cases hp : p.Prime
  · rw [Nat.mem_primeFactors_of_ne_zero hm.ne']
    simp [hp, obstruction_isZero_iff hm hp hk]
  · simp [Nat.mem_primeFactors, hp]

/-- Including divisibility by the discriminant gives the literal finite exceptional set. -/
theorem tor_and_discriminant_support {m d k : ℕ}
    (hm : 0 < m) (hd : d ≠ 0) (hk : 0 < k) :
    {p : ℕ | p.Prime ∧ (¬ IsZero (obstruction m p k) ∨ p ∣ d)} =
      (Paper4ExceptionalPrimeProgression.exceptional m d : Set ℕ) := by
  classical
  ext p
  change (p.Prime ∧ (¬ IsZero (obstruction m p k) ∨ p ∣ d)) ↔
    p ∈ Paper4ExceptionalPrimeProgression.exceptional m d
  by_cases hp : p.Prime
  · rw [Paper4ExceptionalPrimeProgression.prime_mem_exceptional_iff hm.ne' hd hp]
    simp [hp, obstruction_isZero_iff hm hp hk]
  · simp [Paper4ExceptionalPrimeProgression.exceptional, Nat.mem_primeFactors, hp]

/-- Every reduced progression has arbitrarily large primes at which this actual
Tor detector vanishes and the specified discriminant is invertible. -/
theorem exists_large_good_prime {a q m d k : ℕ} (hq : q ≠ 0) (ha : a.Coprime q)
    (hm : 0 < m) (hd : d ≠ 0) (hk : 0 < k) (B : ℕ) :
    ∃ p > B, p.Prime ∧ p ≡ a [MOD q] ∧ IsZero (obstruction m p k) ∧ ¬ p ∣ d := by
  obtain ⟨p, hB, hp, hClass, hM, hD⟩ :=
    Paper4ExceptionalPrimeProgression.exists_large_good_prime hq ha hm.ne' hd B
  exact ⟨p, hB, hp, hClass, (obstruction_isZero_iff hm hp hk).mpr hM, hD⟩

end
end ManuscriptAudit.Paper4NativeTorPrimeSupport

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4NativeTorPrimeSupport.obstruction_isZero_iff,
      ``ManuscriptAudit.Paper4NativeTorPrimeSupport.tor_prime_support,
      ``ManuscriptAudit.Paper4NativeTorPrimeSupport.tor_and_discriminant_support,
      ``ManuscriptAudit.Paper4NativeTorPrimeSupport.exists_large_good_prime] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
