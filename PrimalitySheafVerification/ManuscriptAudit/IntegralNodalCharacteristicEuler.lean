import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalCharacteristicTwoCohomology

/-! Compact Euler jumps between literal geometric fibres of one fixed integral nodal family. -/

namespace ManuscriptAudit.IntegralNodalCharacteristicEuler

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField geometricFiber)
open IntegralNodalGeometricBoundary (geometricSmoothOpen)
open IntegralNodalGeometricPrimePower (affineCompactifyingOpen properHc affineHc smoothHc
  properModelEquiv affineModelEquiv smoothPositiveModelEquiv smoothHZero_subsingleton)
open NodalCompactSupportScalar (extensionModule)
open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

private def properModule (p : ℕ) [Fact p.Prime] (n : ℕ) : Module (ZMod ℓ) (properHc p ℓ n) :=
  extensionModule ℓ (𝟙 (geometricFiber p)) n
private def affineModule (p : ℕ) [Fact p.Prime] (n : ℕ) : Module (ZMod ℓ) (affineHc p ℓ n) :=
  extensionModule ℓ (affineCompactifyingOpen p) n
private def smoothModule (p : ℕ) [Fact p.Prime] (n : ℕ) : Module (ZMod ℓ) (smoothHc p ℓ n) :=
  extensionModule ℓ (geometricSmoothOpen p).ι n

attribute [local instance] properModule affineModule smoothModule

/-- Betti numbers of the literal proper geometric fibre. -/
def properBetti (p : ℕ) [Fact p.Prime] (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (properHc p ℓ n)

/-- Compact Betti numbers of the actual affine chart of that geometric fibre. -/
def affineBetti (p : ℕ) [Fact p.Prime] (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (affineHc p ℓ n)

/-- Compact Betti numbers of the actual relative smooth open of that geometric fibre. -/
def smoothBetti (p : ℕ) [Fact p.Prime] (n : ℕ) : ℕ := Module.finrank (ZMod ℓ) (smoothHc p ℓ n)

private theorem betti_of_equiv {E : Type} [AddCommGroup E] [Module (ZMod ℓ) E]
    {q : Prop} [Decidable q] (e : E ≃+ ZMod (if q then ℓ else 1)) :
    Module.finrank (ZMod ℓ) E = if q then 1 else 0 := by
  by_cases h : q
  · rw [if_pos h]
    let e' : E ≃+ ZMod ℓ := e.trans (ZMod.ringEquivCongr (if_pos h)).toAddEquiv
    let f : E ≃ₗ[ZMod ℓ] ZMod ℓ := LinearEquiv.ofBijective
      (e'.toAddMonoidHom.toZModLinearMap ℓ) e'.bijective
    exact f.finrank_eq.trans (Module.finrank_self _)
  · rw [if_neg h]
    let e' : E ≃+ ZMod 1 := e.trans (ZMod.ringEquivCongr (if_neg h)).toAddEquiv
    letI : Subsingleton E := ⟨fun x y ↦ e'.injective (Subsingleton.elim _ _)⟩
    exact Module.finrank_zero_of_subsingleton

/-- In characteristic two the proper degrees are zero and two, and the two open profiles equal degree two. -/
theorem betti_at_two (hℓ₂ : ℓ ≠ 2) (n : ℕ) :
    properBetti ℓ 2 n = (if n = 0 ∨ n = 2 then 1 else 0) ∧
    affineBetti ℓ 2 n = (if n = 2 then 1 else 0) ∧
    smoothBetti ℓ 2 n = (if n = 2 then 1 else 0) := by
  letI : NeZero (ℓ : closureField 2) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero 2 ℓ hℓ₂⟩
  exact ⟨betti_of_equiv ℓ (IntegralNodalCharacteristicTwoCohomology.properEquiv ℓ n),
    betti_of_equiv ℓ (IntegralNodalCharacteristicTwoCohomology.affineEquiv ℓ n),
    betti_of_equiv ℓ (IntegralNodalCharacteristicTwoCohomology.smoothEquiv ℓ n)⟩

private theorem two_ne_zero (p : ℕ) [Fact p.Prime] (hp : 2 < p) : (2 : closureField p) ≠ 0 :=
  IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)

private def smoothOddEquiv (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    [NeZero (ℓ : closureField p)] (n : ℕ) :
    smoothHc p ℓ n ≃+ ZMod (if n = 1 ∨ n = 2 then ℓ else 1) := by
  cases n with
  | zero =>
    change smoothHc p ℓ 0 ≃+ ZMod 1
    let h := smoothHZero_subsingleton p ℓ
    exact AddEquiv.ofBijective (0 : smoothHc p ℓ 0 →+ ZMod 1)
      ⟨fun x y _ ↦ h.elim x y, fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩
  | succ n =>
    let e := NodalCompactSupportCyclicDegrees.ordinaryEquiv (closureField p) ℓ
      (two_ne_zero p hp) (n + 1)
    let h := NodalCompactSupportCyclicDegrees.positiveOrder ℓ n
    exact (smoothPositiveModelEquiv p ℓ n).trans (e.trans (ZMod.ringEquivCongr h).toAddEquiv)

/-- At odd residue primes, degree one occurs on the proper model and both opens. -/
theorem betti_at_odd (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) (n : ℕ) :
    properBetti ℓ p n = (if n ≤ 2 then 1 else 0) ∧
    affineBetti ℓ p n = (if n = 1 ∨ n = 2 then 1 else 0) ∧
    smoothBetti ℓ p n = (if n = 1 ∨ n = 2 then 1 else 0) := by
  letI : NeZero (ℓ : closureField p) := ⟨IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp⟩
  let h := two_ne_zero p hp
  exact ⟨betti_of_equiv ℓ ((properModelEquiv p ℓ n).trans
    (NodalCompactSupportCyclicDegrees.ordinaryEquiv (closureField p) ℓ h n)),
    betti_of_equiv ℓ ((affineModelEquiv p ℓ n).trans
      (NodalCompactSupportCyclicDegrees.affineEquiv (closureField p) ℓ h n)),
    betti_of_equiv ℓ (smoothOddEquiv ℓ p hp n)⟩

/-- The alternating sum through the given cutoff. -/
def euler (b : ℕ → ℕ) (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (b n : ℤ)

private theorem euler_eq (b : ℕ → ℕ) (N : ℕ) (hN : 3 ≤ N) (hb : ∀ n, 3 ≤ n → b n = 0) :
    euler b N = (b 0 : ℤ) - (b 1 : ℤ) + (b 2 : ℤ) := by
  calc
    _ = euler b 3 := by
      unfold euler
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro i _ hMiss
      have hi : 3 ≤ i := Nat.le_of_not_gt (fun hh ↦ hMiss (Finset.mem_range.mpr hh))
      simp [hb i hi]
    _ = _ := by norm_num [euler, Finset.sum_range_succ, sub_eq_add_neg]

/-- In the literal geometric fibre at (2), the proper, affine, and smooth compact Euler values are 2, 1, and 1. -/
theorem euler_at_two (hℓ₂ : ℓ ≠ 2) (N : ℕ) (hN : 3 ≤ N) :
    euler (properBetti ℓ 2) N = 2 ∧ euler (affineBetti ℓ 2) N = 1 ∧
      euler (smoothBetti ℓ 2) N = 1 := by
  have hP (n : ℕ) := (betti_at_two ℓ hℓ₂ n).1
  have hA (n : ℕ) := (betti_at_two ℓ hℓ₂ n).2.1
  have hS (n : ℕ) := (betti_at_two ℓ hℓ₂ n).2.2
  have h (n : ℕ) (hn : 3 ≤ n) : ¬ (n = 0 ∨ n = 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [euler_eq _ N hN (fun n hn ↦ (hP n).trans (if_neg (h n hn)))]
    norm_num [hP]
  · rw [euler_eq _ N hN (fun n hn ↦ (hA n).trans (if_neg (fun he ↦ h n hn (Or.inr he))))]
    norm_num [hA]
  · rw [euler_eq _ N hN (fun n hn ↦ (hS n).trans (if_neg (fun he ↦ h n hn (Or.inr he))))]
    norm_num [hS]

/-- At any odd residue prime, the same three compact Euler values are 1, 0, and 0. -/
theorem euler_at_odd (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓp : ℓ ≠ p) (N : ℕ) (hN : 3 ≤ N) :
    euler (properBetti ℓ p) N = 1 ∧ euler (affineBetti ℓ p) N = 0 ∧
      euler (smoothBetti ℓ p) N = 0 := by
  have hP (n : ℕ) := (betti_at_odd ℓ p hp hℓp n).1
  have hA (n : ℕ) := (betti_at_odd ℓ p hp hℓp n).2.1
  have hS (n : ℕ) := (betti_at_odd ℓ p hp hℓp n).2.2
  have h (n : ℕ) (hn : 3 ≤ n) : ¬ (n = 1 ∨ n = 2) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [euler_eq _ N hN (fun n hn ↦ (hP n).trans (if_neg (by omega)))]
    norm_num [hP]
  · rw [euler_eq _ N hN (fun n hn ↦ (hA n).trans (if_neg (h n hn)))]
    norm_num [hA]
  · rw [euler_eq _ N hN (fun n hn ↦ (hS n).trans (if_neg (h n hn)))]
    norm_num [hS]

/-- With common prime coefficients, the three characteristic-two compact Euler values
exceed their counterparts at any other residue prime by one. -/
theorem euler_jump (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hℓ₂ : ℓ ≠ 2) (hℓp : ℓ ≠ p)
    (N : ℕ) (hN : 3 ≤ N) :
    euler (properBetti ℓ 2) N - euler (properBetti ℓ p) N = 1 ∧
      euler (affineBetti ℓ 2) N - euler (affineBetti ℓ p) N = 1 ∧
      euler (smoothBetti ℓ 2) N - euler (smoothBetti ℓ p) N = 1 := by
  obtain ⟨heP, heA, heS⟩ := euler_at_two ℓ hℓ₂ N hN
  obtain ⟨hoP, hoA, hoS⟩ := euler_at_odd ℓ p hp hℓp N hN
  norm_num [heP, heA, heS, hoP, hoA, hoS]

end
end ManuscriptAudit.IntegralNodalCharacteristicEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalCharacteristicEuler.betti_at_two,
      ``ManuscriptAudit.IntegralNodalCharacteristicEuler.betti_at_odd,
      ``ManuscriptAudit.IntegralNodalCharacteristicEuler.euler_at_two,
      ``ManuscriptAudit.IntegralNodalCharacteristicEuler.euler_at_odd,
      ``ManuscriptAudit.IntegralNodalCharacteristicEuler.euler_jump] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
