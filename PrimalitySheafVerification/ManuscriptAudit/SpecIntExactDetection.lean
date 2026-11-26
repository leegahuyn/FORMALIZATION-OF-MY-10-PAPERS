import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ClosedPointSupportDetection
import PrimalitySheafVerification.ManuscriptAudit.CofiniteSupportDetection

/-!
# The exact-support detection index on Spec ℤ

This is the value of the native sheaf-cohomology infimum in Paper 6,
physical p. 200, Definition 7.1, with the infimum of the empty set
taken to be infinity.
-/

namespace ManuscriptAudit.SpecIntExactDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.ExactSupportDetection

noncomputable section

private abbrev X := TopCat.of (PrimeSpectrum ℤ)

local instance (S : TopCat.{0}) : HasExt.{0} (AbelianSheaf S) :=
  IsGrothendieckAbelian.hasExt _

/-- A support containing the generic point with infinite complement has no sheaf witness. -/
theorem no_support_of_generic_and_infinite_compl {P : Set (PrimeSpectrum ℤ)}
    (hη : (⊥ : PrimeSpectrum ℤ) ∈ P) (hFin : ¬ (Pᶜ).Finite) :
    ¬ ∃ F : AbelianSheaf X, stalkSupport F = P := by
  rintro ⟨F, hF⟩
  have hη' : (⊥ : PrimeSpectrum ℤ) ∈ stalkSupport F := hF.symm ▸ hη
  have h := GenericPointSupportDetection.specInt_stalkSupport_compl_finite_of_generic_mem F hη'
  rw [hF] at h
  exact hFin h

private theorem index_eq_top_of_no_support {S : TopCat.{0}} {P : Set S}
    (h : ¬ ∃ F : AbelianSheaf S, stalkSupport F = P) : exactDetectionIndex S P = ⊤ := by
  unfold exactDetectionIndex
  have hEmpty : {i : ℕ∞ | ∃ n : ℕ, (n : ℕ∞) = i ∧
      ∃ F : AbelianSheaf S, stalkSupport F = P ∧ Nontrivial (F.H n)} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun i hi => ?_
    obtain ⟨n, -, F, hF, hH⟩ := hi
    exact h ⟨F, hF⟩
  rw [hEmpty, sInf_empty]

/-- The infimum is zero precisely for nonempty supports avoiding the generic
point, or for supports containing it whose complement is finite. -/
theorem specInt_exactDetectionIndex_classification (P : Set (PrimeSpectrum ℤ)) :
    exactDetectionIndex X P =
      @ite ℕ∞ (P.Nonempty ∧ ((⊥ : PrimeSpectrum ℤ) ∉ P ∨ (Pᶜ).Finite))
        (Classical.propDecidable _) 0 ⊤ := by
  classical
  by_cases hNonempty : P.Nonempty
  · by_cases hη : (⊥ : PrimeSpectrum ℤ) ∈ P
    · by_cases hFin : (Pᶜ).Finite
      · rw [if_pos ⟨hNonempty, Or.inr hFin⟩]
        exact CofiniteSupportDetection.specInt_exactDetectionIndex_eq_zero_of_cofinite_generic hη hFin
      · rw [if_neg (by simp [hη, hFin])]
        exact index_eq_top_of_no_support (no_support_of_generic_and_infinite_compl hη hFin)
    · rw [if_pos ⟨hNonempty, Or.inl hη⟩]
      apply ClosedPointSupportDetection.specInt_exactDetectionIndex_eq_zero _ hNonempty
      intro x hx hBot
      have hx' : x = ⊥ := PrimeSpectrum.ext_iff.mpr (hBot.trans PrimeSpectrum.asIdeal_bot.symm)
      exact hη (hx' ▸ hx)
  · have hEmpty : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hNonempty
    rw [if_neg (fun h => hNonempty h.1), hEmpty]
    exact exactDetectionIndex_empty X

/-- In particular the value 1 in the worked model on physical p. 202 is impossible. -/
theorem paper6_worked_model_value_refuted (P : Set (PrimeSpectrum ℤ)) :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) P ≠ 1 := by
  classical
  rw [specInt_exactDetectionIndex_classification]
  split <;> simp

end

end ManuscriptAudit.SpecIntExactDetection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntExactDetection.no_support_of_generic_and_infinite_compl,
      ``ManuscriptAudit.SpecIntExactDetection.specInt_exactDetectionIndex_classification,
      ``ManuscriptAudit.SpecIntExactDetection.paper6_worked_model_value_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
