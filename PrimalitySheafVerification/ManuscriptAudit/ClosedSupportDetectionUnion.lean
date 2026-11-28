import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ClosedSupportDetection

/-! Paper 4, physical pp. 114–119 and 136: exact closed-support indices,
their behavior on unions, and the precise condition for invariance under shrinking. -/

namespace ManuscriptAudit.ClosedSupportDetectionUnion

open CategoryTheory TopologicalSpace ClosedSupportDetection

noncomputable section

theorem detectionIndex_closed (X : TopCat.{0}) {P : Set X} (hP : IsClosed P) :
    detectionIndex X P = @ite ℕ∞ P.Nonempty (Classical.propDecidable _) 0 ⊤ := by
  classical
  by_cases h : P.Nonempty
  · rw [if_pos h]
    exact detectionIndex_eq_zero_of_nonempty_closed X hP h
  · rw [if_neg h, Set.not_nonempty_iff_eq_empty.mp h]
    exact detectionIndex_empty X

/-- The exact infimum for a union of closed supports is the smaller value. -/
theorem detectionIndex_union_eq_min (X : TopCat.{0}) {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q) :
    detectionIndex X (P ∪ Q) = min (detectionIndex X P) (detectionIndex X Q) := by
  classical
  rw [detectionIndex_closed X (hP.union hQ), detectionIndex_closed X hP,
    detectionIndex_closed X hQ, Set.union_nonempty]
  by_cases h1 : P.Nonempty <;> by_cases h2 : Q.Nonempty <;> simp [h1, h2]

/-- The printed sharper upper bound holds for every pair of closed supports. -/
theorem detectionIndex_union_le_max (X : TopCat.{0}) (P Q : Set X) :
    detectionIndex X (P ∪ Q) ≤ max (detectionIndex X P) (detectionIndex X Q) :=
  ((detectionIndex_antitone X) Set.subset_union_left).trans (le_max_left _ _)

/-- An open restriction preserves the closed-support index exactly when the
original support is empty or at least one of its points remains. -/
theorem detectionIndex_open_restriction_eq_iff (X : TopCat.{0}) {P : Set X}
    (hP : IsClosed P) (U : Opens X) :
    detectionIndex (TopCat.of U) ((Subtype.val : U → X) ⁻¹' P) = detectionIndex X P ↔
      P = ∅ ∨ ((U : Set X) ∩ P).Nonempty := by
  classical
  have hMeet : ((Subtype.val : U → X) ⁻¹' P).Nonempty ↔ ((U : Set X) ∩ P).Nonempty :=
    ⟨fun ⟨x, hx⟩ ↦ ⟨x.val, x.property, hx⟩, fun ⟨x, hx, hp⟩ ↦ ⟨⟨x, hx⟩, hp⟩⟩
  rw [detectionIndex_closed (TopCat.of U) (hP.preimage continuous_subtype_val),
    detectionIndex_closed X hP]
  by_cases hPne : P.Nonempty
  · by_cases hU : ((U : Set X) ∩ P).Nonempty
    · simp [hPne, hMeet.mpr hU, hU]
    · have hPreimage : ¬ ((Subtype.val : U → X) ⁻¹' P).Nonempty := fun h ↦ hU (hMeet.mp h)
      simp [hPne, hPne.ne_empty, hPreimage, hU]
  · have hE := Set.not_nonempty_iff_eq_empty.mp hPne
    simp [hE]

/-- A closed point has index zero for the support-contained definition. -/
theorem detectionIndex_closed_point (X : TopCat.{0}) (p : X)
    (hp : IsClosed ({p} : Set X)) : detectionIndex X {p} = 0 :=
  detectionIndex_eq_zero_of_nonempty_closed X hp ⟨p, Set.mem_singleton p⟩

end
end ManuscriptAudit.ClosedSupportDetectionUnion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ClosedSupportDetectionUnion.detectionIndex_closed,
      ``ManuscriptAudit.ClosedSupportDetectionUnion.detectionIndex_union_eq_min,
      ``ManuscriptAudit.ClosedSupportDetectionUnion.detectionIndex_union_le_max,
      ``ManuscriptAudit.ClosedSupportDetectionUnion.detectionIndex_open_restriction_eq_iff,
      ``ManuscriptAudit.ClosedSupportDetectionUnion.detectionIndex_closed_point] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
