import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverHOne
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCuspHOne

/-!
# The affine node and its normalization have different ordinary H¹

For an algebraically closed field of characteristic different from two
the normalizing affine line has zero ordinary étale H¹ with constant
Z/2. The actual crossed étale cover gives a nonzero class on the node.
-/

namespace ManuscriptAudit.NodalNormalizationHOneComparison

open AlgebraicGeometry CategoryTheory NodalConductor

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev cohomology (R : CommRingCat.{0}) :=
  Sheaf.H ((constantSheaf (Spec R).smallEtaleTopology AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ZMod 2))) 1

abbrev nodeHOne := cohomology (CommRingCat.of ↥(coordinates K))

abbrev normalizationHOne := cohomology (CommRingCat.of (Polynomial K))

theorem normalization_HOne_subsingleton (h2 : (2 : K) ≠ 0) :
    Subsingleton (normalizationHOne K) := by
  letI : NeZero (((2 : ℕ) : K)) := ⟨by simpa using h2⟩
  exact SmallEtaleCuspHOne.affineLine_cyclic_HOne_subsingleton K 2

/-- The actual ordinary small étale groups differ for the node and its normalization. -/
theorem no_HOne_equivalence (h2 : (2 : K) ≠ 0) :
    IsEmpty (nodeHOne K ≃ normalizationHOne K) := by
  refine ⟨fun e => ?_⟩
  letI : Nontrivial (nodeHOne K) := NodalSwapCoverHOne.full_constant_HOne_nontrivial K h2
  letI : Subsingleton (normalizationHOne K) := normalization_HOne_subsingleton K h2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (α := nodeHOne K)
  exact hxy (e.injective (Subsingleton.elim _ _))

end

end ManuscriptAudit.NodalNormalizationHOneComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.NodalNormalizationHOneComparison.normalization_HOne_subsingleton,
      ``ManuscriptAudit.NodalNormalizationHOneComparison.no_HOne_equivalence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
