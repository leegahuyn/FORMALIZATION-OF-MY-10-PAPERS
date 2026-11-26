import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsionLowerBound

/-!
# Distinct actual geometric torsion types on every nonempty principal open

For the printed cubic family with A = 1, every nonempty principal open of
Spec ℤ contains arbitrarily large primes with nontrivial geometric
p-torsion and arbitrarily large primes with trivial geometric p-torsion.
Consequently no such open supports a fixed underlying fiber type.
-/

namespace ManuscriptAudit.CubicGeometricTorsionOnSpecInt

open CubicGeometricTorsionLowerBound
open TopologicalSpace

abbrev primePoint (p : ℕ) (hp : p.Prime) : PrimeSpectrum ℤ :=
  letI : Fact p.Prime := ⟨hp⟩
  PrimeSpectrum.comap (Int.castRingHom (ZMod p)) (⊥ : PrimeSpectrum (ZMod p))

abbrev torsionFiber (p : ℕ) (hp : p.Prime) : Type :=
  letI : Fact p.Prime := ⟨hp⟩
  geometricPTorsion p (1 : ZMod p)

theorem torsionFiber_subsingleton_iff {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Subsingleton (torsionFiber p hp) ↔ p % 3 = 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hClass := CubicGeometricClassification.paper5_trivial_geometric_p_torsion_iff
    hp5 (one_ne_zero : (1 : ZMod p) ≠ 0)
  rw [← hClass]
  constructor
  · intro hs P hP
    exact congrArg Subtype.val (hs.elim ⟨P, hP⟩ ⟨0, nsmul_zero p⟩)
  · intro h
    constructor
    intro P Q
    exact Subtype.ext ((h P.val P.property).trans (h Q.val Q.property).symm)

theorem basicOpen_contains_prime_modEq_above (m : ℤ) (hm : m ≠ 0) (N : ℕ)
    {a : ℕ} (ha : a.Coprime 3) :
    ∃ p, ∃ hp : p.Prime, N < p ∧ p ≡ a [MOD 3] ∧ primePoint p hp ∈ PrimeSpectrum.basicOpen m := by
  obtain ⟨p, hLarge, hp, hClass⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N m.natAbs) (q := 3) (a := a)
      (by decide) ha
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, (le_max_left N m.natAbs).trans_lt hLarge, hClass, ?_⟩
  change ¬ (m : ZMod p) ∈ (⊥ : Ideal (ZMod p))
  rw [Ideal.mem_bot]
  intro hz
  have hdiv : (p : ℤ) ∣ m := (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp hz
  have hNat : p ∣ m.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
  have hsmall := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) hNat
  exact (not_lt_of_ge hsmall) ((le_max_right N m.natAbs).trans_lt hLarge)

theorem basicOpen_contains_both_torsion_types (m : ℤ) (hm : m ≠ 0) (N : ℕ) :
    (∃ p, ∃ hp : p.Prime, N < p ∧ primePoint p hp ∈ PrimeSpectrum.basicOpen m ∧
      ¬ Subsingleton (torsionFiber p hp)) ∧
    (∃ p, ∃ hp : p.Prime, N < p ∧ primePoint p hp ∈ PrimeSpectrum.basicOpen m ∧
      Subsingleton (torsionFiber p hp)) := by
  constructor
  · obtain ⟨p, hp, hN, hMod, hOpen⟩ :=
      basicOpen_contains_prime_modEq_above m hm (max N 4) (a := 1) (by decide)
    have hp5 : 5 ≤ p := (le_max_right N 4).trans_lt hN
    have hOne : p % 3 = 1 := by simpa [Nat.ModEq] using hMod
    refine ⟨p, hp, (le_max_left N 4).trans_lt hN, hOpen, ?_⟩
    rw [torsionFiber_subsingleton_iff hp hp5, hOne]
    decide
  · obtain ⟨p, hp, hN, hMod, hOpen⟩ :=
      basicOpen_contains_prime_modEq_above m hm (max N 4) (a := 2) (by decide)
    have hp5 : 5 ≤ p := (le_max_right N 4).trans_lt hN
    have hTwo : p % 3 = 2 := by simpa [Nat.ModEq] using hMod
    exact ⟨p, hp, (le_max_left N 4).trans_lt hN, hOpen,
      (torsionFiber_subsingleton_iff hp hp5).mpr hTwo⟩

theorem no_fixed_torsionFiber_type_on_basicOpen (m : ℤ) (hm : m ≠ 0) :
    ¬ ∃ T : Type, ∀ (p : ℕ) (hp : p.Prime), primePoint p hp ∈ PrimeSpectrum.basicOpen m →
      Nonempty (torsionFiber p hp ≃ T) := by
  rintro ⟨T, hT⟩
  obtain ⟨⟨p, hp, _, hpOpen, hNontriv⟩, ⟨q, hq, _, hqOpen, hTriv⟩⟩ :=
    basicOpen_contains_both_torsion_types m hm 0
  obtain ⟨ep⟩ := hT p hp hpOpen
  obtain ⟨eq⟩ := hT q hq hqOpen
  exact hNontriv ⟨fun x y =>
    ep.injective (eq.symm.injective (hTriv.elim (eq.symm (ep x)) (eq.symm (ep y))))⟩

theorem no_fixed_torsionFiber_type_on_genericOpen (U : Opens (PrimeSpectrum ℤ))
    (hU : (⊥ : PrimeSpectrum ℤ) ∈ U) :
    ¬ ∃ T : Type, ∀ (p : ℕ) (hp : p.Prime), primePoint p hp ∈ U →
      Nonempty (torsionFiber p hp ≃ T) := by
  rintro ⟨T, hT⟩
  obtain ⟨_, ⟨m, rfl⟩, hm, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hU U.isOpen
  have hm' : m ≠ 0 := by
    simpa only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hm
  exact no_fixed_torsionFiber_type_on_basicOpen m hm' ⟨T, fun p hp h => hT p hp (hsub h)⟩

end ManuscriptAudit.CubicGeometricTorsionOnSpecInt

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.CubicGeometricTorsionOnSpecInt.torsionFiber_subsingleton_iff,
        ``ManuscriptAudit.CubicGeometricTorsionOnSpecInt.basicOpen_contains_prime_modEq_above,
        ``ManuscriptAudit.CubicGeometricTorsionOnSpecInt.basicOpen_contains_both_torsion_types,
        ``ManuscriptAudit.CubicGeometricTorsionOnSpecInt.no_fixed_torsionFiber_type_on_basicOpen,
        ``ManuscriptAudit.CubicGeometricTorsionOnSpecInt.no_fixed_torsionFiber_type_on_genericOpen] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
