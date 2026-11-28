import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SpecIntExactDetection
import PrimalitySheafVerification.ManuscriptAudit.ClosedSupportDetectionUnion

/-! The two support quantifiers printed on Paper 4, physical p. 114,
give the same actual detection index on closed subsets of Spec ℤ. -/

namespace ManuscriptAudit.SpecIntClosedDetectionComparison

open ClosedSupportDetection ClosedSupportDetectionUnion ExactSupportDetection

noncomputable section

theorem exact_eq_contained_of_closed (P : Set (PrimeSpectrum ℤ)) (hP : IsClosed P) :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) P =
      detectionIndex (TopCat.of (PrimeSpectrum ℤ)) P := by
  classical
  rw [SpecIntExactDetection.specInt_exactDetectionIndex_classification,
    detectionIndex_closed _ hP]
  by_cases hη : (⊥ : PrimeSpectrum ℤ) ∈ P
  · have hAll : P = Set.univ := by
      apply Set.eq_univ_of_forall
      intro p
      have h : Specializes (⊥ : PrimeSpectrum ℤ) p :=
        (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
      exact h.mem_closed hP hη
    simp [hAll]
  · simp [hη]

end
end ManuscriptAudit.SpecIntClosedDetectionComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SpecIntClosedDetectionComparison.exact_eq_contained_of_closed
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
