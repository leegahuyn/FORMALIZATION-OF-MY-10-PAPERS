import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.Skyscraper

/-!
Paper 4, physical p. 114, Proposition 3.19(ii) states that shrinking to
a principal open cannot destroy sections in degree zero. The skyscraper
abelian sheaf at (2) has nonzero sections on Spec ℤ and zero sections on
every open contained in D(2).
-/

namespace ManuscriptAudit.PrincipalOpenSectionLoss

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

local notation "S" => TopCat.of (PrimeSpectrum ℤ)
private abbrev G := AddCommGrpCat.{0}
local notation "D₂" => PrimeSpectrum.basicOpen (2 : ℤ)

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (1 < (2 : ℕ)) := ⟨by decide⟩

/-- The closed point of Spec ℤ defined by the prime integer 2. -/
def closedTwo : S :=
  ⟨Ideal.span ({((2 : ℕ) : ℤ)} : Set ℤ), (Int.ideal_span_isMaximal_of_prime 2).isPrime⟩

theorem closedTwo_isClosed : IsClosed ({closedTwo} : Set (PrimeSpectrum ℤ)) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal closedTwo).2
    (Int.ideal_span_isMaximal_of_prime 2)

theorem closedTwo_not_mem_D2 : closedTwo ∉ D₂ := by
  intro h
  exact (PrimeSpectrum.mem_basicOpen 2 closedTwo).mp h (Ideal.mem_span_singleton_self _)

/-- The abelian skyscraper sheaf with value ℤ/2 at the point (2). -/
def skyscraperAtTwo : TopCat.Sheaf G S := by
  classical
  exact skyscraperSheaf closedTwo (AddCommGrpCat.of (ZMod 2))

theorem skyscraperAtTwo_globalSections :
    skyscraperAtTwo.obj.obj (op (⊤ : Opens S)) = AddCommGrpCat.of (ZMod 2) := by
  classical
  change (if closedTwo ∈ (⊤ : Opens S) then AddCommGrpCat.of (ZMod 2) else terminal G) = _
  rw [if_pos (show closedTwo ∈ (⊤ : Opens S) by simp)]

theorem skyscraperAtTwo_sections_below_D2 {U : Opens S} (hU : U ≤ D₂) :
    skyscraperAtTwo.obj.obj (op U) = terminal G := by
  classical
  change (if closedTwo ∈ U then AddCommGrpCat.of (ZMod 2) else terminal G) = _
  rw [if_neg (fun h => closedTwo_not_mem_D2 (hU h))]

private theorem terminalGroup_subsingleton : Subsingleton (terminal G) := by
  have hZero : IsZero (0 : G) := isZero_zero G
  exact AddCommGrpCat.subsingleton_of_isZero
    (hZero.of_iso (terminalIsoIsTerminal hZero.isTerminal))

theorem skyscraperAtTwo_stalkSupport :
    {x : S | Nontrivial (skyscraperAtTwo.obj.stalk x)} = {closedTwo} := by
  classical
  ext x
  by_cases hx : x = closedTwo
  · subst x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, iff_true]
    let e := skyscraperPresheafStalkOfSpecializes closedTwo
      (AddCommGrpCat.of (ZMod 2)) (specializes_rfl : Specializes closedTwo closedTwo)
    exact (e.symm.addCommGroupIsoToAddEquiv).injective.nontrivial
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hx, iff_false]
    have hs : ¬ Specializes closedTwo x := by
      intro h
      exact hx (h.mem_closed closedTwo_isClosed (Set.mem_singleton closedTwo))
    let e := skyscraperPresheafStalkOfNotSpecializes closedTwo
      (AddCommGrpCat.of (ZMod 2)) hs
    letI : Subsingleton (terminal G) := terminalGroup_subsingleton
    letI : Subsingleton (skyscraperAtTwo.obj.stalk x) :=
      (e.addCommGroupIsoToAddEquiv).injective.subsingleton
    rintro ⟨a, b, hab⟩
    exact hab (Subsingleton.elim a b)

/-- An actual nonzero degree-zero section disappears on shrinking to D(2). -/
theorem paper4_principalOpenRestriction_destroys_section :
    ∃ s : skyscraperAtTwo.obj.obj (op (⊤ : Opens S)), s ≠ 0 ∧
      (skyscraperAtTwo.obj.map (homOfLE (le_top : D₂ ≤ (⊤ : Opens S))).op) s = 0 := by
  letI : Nontrivial (skyscraperAtTwo.obj.obj (op (⊤ : Opens S))) := by
    rw [skyscraperAtTwo_globalSections]
    change Nontrivial (ZMod 2)
    infer_instance
  letI : Subsingleton (skyscraperAtTwo.obj.obj (op D₂)) := by
    rw [skyscraperAtTwo_sections_below_D2 (U := D₂) le_rfl]
    exact terminalGroup_subsingleton
  obtain ⟨s, hs⟩ := exists_ne (0 : skyscraperAtTwo.obj.obj (op (⊤ : Opens S)))
  exact ⟨s, hs, Subsingleton.elim _ _⟩

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``closedTwo_isClosed, ``closedTwo_not_mem_D2, ``skyscraperAtTwo_globalSections,
      ``skyscraperAtTwo_sections_below_D2, ``skyscraperAtTwo_stalkSupport,
      ``paper4_principalOpenRestriction_destroys_section] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.PrincipalOpenSectionLoss
