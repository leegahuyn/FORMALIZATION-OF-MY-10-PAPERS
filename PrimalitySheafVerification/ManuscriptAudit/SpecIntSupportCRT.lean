import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.SpecIntOpenSupport
import PrimalitySheafVerification.ManuscriptAudit.SpecIntSupportReduction

/-!
# Exact support on the CRT opens at 2 and 3

Paper 6, Proposition 7.2(3) on physical p. 201, compares index statements
on the intersection with paired statements on the covering opens. The
support consisting of the closed point (3) gives different truth values
for the statement that the exact-support index is infinite.
-/

namespace ManuscriptAudit.SpecIntSupportCRT

open TopologicalSpace
open ManuscriptAudit.ExactSupportDetection
open ManuscriptAudit.SpecIntSupportReduction

noncomputable section

private abbrev X := PrimeSpectrum ℤ
private abbrev D (n : ℤ) : Opens X := PrimeSpectrum.basicOpen n

/-- The exact index of the inverse image of the support `{(3)}` in an open. -/
def restrictionIndex (U : Opens X) : ℕ∞ :=
  exactDetectionIndex (TopCat.of U) ((Subtype.val : U → X) ⁻¹' {primeThree})

/-- The CRT opens cover Spec ℤ and their intersection is the principal open at 6. -/
theorem crt_cover_and_intersection :
    IsCoprime (2 : ℤ) 3 ∧ D 2 ⊔ D 3 = ⊤ ∧ D 6 = D 2 ⊓ D 3 := by
  refine ⟨⟨-1, 1, by norm_num⟩, ?_, ?_⟩
  · apply le_antisymm le_top
    intro x _
    change x ∈ D 2 ⊔ D 3
    apply Opens.mem_sup.mpr
    by_cases h2 : (2 : ℤ) ∈ x.asIdeal
    · right
      apply (PrimeSpectrum.mem_basicOpen (3 : ℤ) x).2
      intro h3
      have h : (1 : ℤ) ∈ x.asIdeal := by
        simpa only [show (3 : ℤ) - 2 = 1 by decide] using x.asIdeal.sub_mem h3 h2
      exact x.2.ne_top ((Ideal.eq_top_iff_one x.asIdeal).mpr h)
    · exact Or.inl ((PrimeSpectrum.mem_basicOpen (2 : ℤ) x).2 h2)
  · simpa only [show (2 : ℤ) * 3 = 6 by decide] using
      PrimeSpectrum.basicOpen_mul (2 : ℤ) 3

private theorem restrictionIndex_zero {U : Opens X} (hU : primeThree ∈ U) :
    restrictionIndex U = 0 := by
  let P : Set U := (Subtype.val : U → X) ⁻¹' {primeThree}
  have hImage : (Subtype.val '' P : Set X) = {primeThree} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      have h : x = primeThree := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨primeThree, hU⟩, Set.mem_singleton _, rfl⟩
  have hIndex := SpecIntOpenSupport.exactDetectionIndex_restriction U P
  rw [hImage] at hIndex
  have hAmbient : exactDetectionIndex (TopCat.of X) {primeThree} = 0 :=
    exactDetectionIndex_eq_zero_of_nonempty_closed
      (X := TopCat.of X) (P := {primeThree})
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal primeThree).2
        (IsPrime.to_maximal_ideal primeThree_ne_generic))
      (Set.singleton_nonempty primeThree)
  exact hIndex.symm.trans hAmbient

private theorem restrictionIndex_top {U : Opens X} (hU : primeThree ∉ U) :
    restrictionIndex U = ⊤ := by
  have hEmpty : ((Subtype.val : U → X) ⁻¹' {primeThree}) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    have hx' : x.val = primeThree := Set.mem_singleton_iff.mp hx
    exact hU (hx' ▸ x.property)
  unfold restrictionIndex
  rw [hEmpty, exactDetectionIndex_empty]

/-- The actual index values of the prescribed support on the three CRT opens. -/
theorem restrictionIndex_two_three_six :
    restrictionIndex (D 2) = 0 ∧ restrictionIndex (D 3) = ⊤ ∧
      restrictionIndex (D 6) = ⊤ := by
  have h2 : primeThree ∈ D 2 := (PrimeSpectrum.mem_basicOpen _ _).2 two_not_mem_primeThree
  have h3 : primeThree ∉ D 3 := fun h => (PrimeSpectrum.mem_basicOpen _ _).1 h three_mem_primeThree
  have h6 : primeThree ∉ D 6 := by
    rw [crt_cover_and_intersection.2.2]
    exact fun h => h3 (Opens.mem_inf.mp h).2
  exact ⟨restrictionIndex_zero h2, restrictionIndex_top h3, restrictionIndex_top h6⟩

/-- At coprime 2 and 3, the infinite-index statement on the intersection
does not agree with the conjunction of the two infinite-index statements. -/
theorem paper6_proposition7_2_crt_refuted :
    ¬ (restrictionIndex (D 6) = ⊤ ↔
      restrictionIndex (D 2) = ⊤ ∧ restrictionIndex (D 3) = ⊤) := by
  obtain ⟨h2, h3, h6⟩ := restrictionIndex_two_three_six
  rw [h2, h3, h6]
  simp

end

end ManuscriptAudit.SpecIntSupportCRT

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntSupportCRT.crt_cover_and_intersection,
      ``ManuscriptAudit.SpecIntSupportCRT.restrictionIndex_two_three_six,
      ``ManuscriptAudit.SpecIntSupportCRT.paper6_proposition7_2_crt_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
