import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Nullstellensatz

/-!
# A nonzero common point for a short system of polynomial equations

A system over an algebraically closed field that vanishes at the origin
cannot cut out that point alone if it has fewer equations than variables.
This is the dimension-counting ingredient in the proof of Tsen's theorem.
-/

namespace ManuscriptAudit.PolynomialCommonZero

open MvPolynomial

noncomputable section

variable (K : Type*) [Field K]

private def eraseInitial (n j : ℕ) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun i : Fin n => if i.val < j then 0 else X i

private abbrev coordinateIdeal (n j : ℕ) : Ideal (MvPolynomial (Fin n) K) :=
  RingHom.ker (eraseInitial K n j).toRingHom

private theorem coordinateIdeal_prime (n j : ℕ) : (coordinateIdeal K n j).IsPrime :=
  RingHom.ker_isPrime _

private theorem coordinateIdeal_lt (n j : ℕ) (hj : j < n) :
    coordinateIdeal K n j < coordinateIdeal K n (j + 1) := by
  have hcomp : (eraseInitial K n (j + 1)).comp (eraseInitial K n j) =
      eraseInitial K n (j + 1) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i.val < j
    · have hi' : i.val < j + 1 := Nat.lt_succ_of_lt hi
      simp only [eraseInitial, AlgHom.comp_apply, aeval_X, if_pos hi, if_pos hi', map_zero]
    · simp only [eraseInitial, AlgHom.comp_apply, aeval_X, if_neg hi]
  apply lt_of_le_not_ge
  · intro f hf
    change eraseInitial K n j f = 0 at hf
    change eraseInitial K n (j + 1) f = 0
    rw [← hcomp, AlgHom.comp_apply, hf, map_zero]
  · intro h
    let i : Fin n := ⟨j, hj⟩
    have hmem : X i ∈ coordinateIdeal K n (j + 1) := by
      change eraseInitial K n (j + 1) (X i) = 0
      simp [eraseInitial, i]
    have hi : eraseInitial K n j (X i) = 0 := h hmem
    exact X_ne_zero (R := K) i (by simpa [eraseInitial, i] using hi)

private theorem coordinateIdeal_height (n j : ℕ) (hj : j ≤ n) :
    (j : ℕ∞) ≤ (coordinateIdeal K n j).height := by
  induction j with
  | zero => exact zero_le
  | succ j ih =>
    letI : (coordinateIdeal K n j).IsPrime := coordinateIdeal_prime K n j
    letI : (coordinateIdeal K n (j + 1)).IsPrime := coordinateIdeal_prime K n (j + 1)
    have h := Ideal.height_add_one_le_of_lt_of_isPrime
      (coordinateIdeal_lt K n j (Nat.lt_of_succ_le hj))
    have h₀ : (j : ℕ∞) + 1 ≤ (coordinateIdeal K n j).height + 1 :=
      add_le_add (ih (Nat.le_of_succ_le hj)) le_rfl
    have hle := h₀.trans h
    simpa only [Nat.cast_succ] using hle

private theorem coordinateIdeal_eq_vanishingIdeal_zero (n : ℕ) :
    coordinateIdeal K n n = vanishingIdeal K ({0} : Set (Fin n → K)) := by
  let c : K →ₐ[K] MvPolynomial (Fin n) K := Algebra.ofId K _
  have he : eraseInitial K n n = c.comp (aeval (0 : Fin n → K)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [eraseInitial]
  ext f
  rw [mem_vanishingIdeal_singleton_iff]
  change eraseInitial K n n f = 0 ↔ aeval (0 : Fin n → K) f = 0
  rw [he, AlgHom.comp_apply]
  exact MvPolynomial.C_eq_zero

/-- Fewer equations than variables admit a common nonzero point over an
algebraically closed field, if all the equations vanish at zero. -/
theorem exists_nonzero_common_zero [IsAlgClosed K] {n m : ℕ}
    (hcard : m < n) (f : Fin m → MvPolynomial (Fin n) K)
    (h₀ : ∀ i, aeval (0 : Fin n → K) (f i) = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ i, aeval x (f i) = 0 := by
  classical
  by_contra h
  let s : Finset (MvPolynomial (Fin n) K) := Finset.univ.image f
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span (s : Set _)
  let M : Ideal (MvPolynomial (Fin n) K) := vanishingIdeal K ({0} : Set (Fin n → K))
  have hs : (s : Set (MvPolynomial (Fin n) K)) = Set.range f := by
    ext p
    simp [s]
  have hPoint : zeroLocus K I = ({0} : Set (Fin n → K)) := by
    rw [show I = Ideal.span (s : Set _) from rfl, zeroLocus_span, hs]
    ext x
    change (∀ p ∈ Set.range f, aeval x p = 0) ↔ x ∈ ({0} : Set (Fin n → K))
    rw [Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      exact h ⟨x, hne, fun i => hx _ ⟨i, rfl⟩⟩
    · rintro rfl _ ⟨i, rfl⟩
      exact h₀ i
  have hRad : I.radical = M := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K) I, hPoint]
  have hPrime : M.IsPrime := inferInstance
  have hMinimal : M ∈ I.minimalPrimes := by
    refine ⟨⟨hPrime, ?_⟩, ?_⟩
    · rw [← hRad]
      exact I.le_radical
    · intro J hJ _
      rw [← hRad]
      exact hJ.1.radical_le_iff.mpr hJ.2
  have hLower : (n : ℕ∞) ≤ M.height := by
    change (n : ℕ∞) ≤ (vanishingIdeal K ({0} : Set (Fin n → K))).height
    rw [← coordinateIdeal_eq_vanishingIdeal_zero K n]
    exact coordinateIdeal_height K n n le_rfl
  have hUpper : M.height ≤ s.card :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset hMinimal
  have hsCard : s.card ≤ m := by
    simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := f))
  exact (Nat.not_le_of_lt hcard) ((ENat.coe_le_coe.mp (hLower.trans hUpper)).trans hsCard)

end

end ManuscriptAudit.PolynomialCommonZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.PolynomialCommonZero.exists_nonzero_common_zero
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
