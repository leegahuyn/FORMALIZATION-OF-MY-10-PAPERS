import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOneRestriction
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusCohomology

/-! Exact ordinary and compactly supported mod-two degree-one étale
cohomology of the actual split nodal model over an algebraically closed field. -/

namespace ManuscriptAudit.NodalProjectiveHOneExact

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure NodalCompactSupportHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.of (ZMod 2)
abbrev projectiveHOne :=
  Sheaf.H ((constantSheaf (projectiveNode K).smallEtaleTopology AddCommGrpCat.{0}).obj A) 1

private theorem nonzero_zmod_two_eq_one (a : ZMod 2) (ha : a ≠ 0) : a = 1 :=
  (show ∀ b : ZMod 2, b ≠ 0 → b = 1 by decide) a ha

/-- The actual ordinary étale H¹ of the proper node is precisely one copy of Z/2. -/
def projectiveHOneEquiv (h2 : (2 : K) ≠ 0) : projectiveHOne K ≃+ ZMod 2 := by
  let e := NodalConductorHOne.affineHOneEquiv K h2
  let r := NodalProjectiveHOneRestriction.restriction K
  let u : projectiveHOne K →+ ZMod 2 := e.symm.toAddMonoidHom.comp r
  have hi : Function.Injective u :=
    e.symm.injective.comp (NodalProjectiveHOneRestriction.restriction_injective K h2)
  have hNT := NodalProjectiveHOne.projectiveNode_HOne_nontrivial K h2
  obtain ⟨x, y, hxy⟩ := hNT.exists_pair_ne
  let z := x - y
  have hz : z ≠ 0 := fun h => hxy (sub_eq_zero.mp h)
  have h1 : u z = 1 :=
    nonzero_zmod_two_eq_one (u z) (fun h => hz (hi (h.trans (map_zero u).symm)))
  refine AddEquiv.ofBijective u ⟨hi, ?_⟩
  intro a
  by_cases ha : a = 0
  · exact ⟨0, (map_zero u).trans ha.symm⟩
  · exact ⟨z, h1.trans (nonzero_zmod_two_eq_one a ha).symm⟩

/-- The actual affine node has the same single compactly supported mod-two class. -/
def compactHOneEquiv (h2 : (2 : K) ≠ 0) :
    nodalHc K A 1 ≃+ ZMod 2 :=
  (nodalHcOneProjectiveEquiv K A).trans (projectiveHOneEquiv K h2)

/-- The ordinary mod-two degree-one groups of the proper node and its smooth locus
are additively isomorphic. -/
def properSmoothHOneEquiv (h2 : (2 : K) ≠ 0) :
    projectiveHOne K ≃+
      Sheaf.H ((constantSheaf (NodalSmoothLocusOverlap.smoothScheme K).smallEtaleTopology
        AddCommGrpCat.{0}).obj A) 1 := by
  letI : NeZero (2 : K) := ⟨h2⟩
  exact (projectiveHOneEquiv K h2).trans
    (NodalSmoothLocusCohomology.smoothLocusCyclicHOneEquiv K h2 2 (by decide))

end
end ManuscriptAudit.NodalProjectiveHOneExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveHOneExact.projectiveHOneEquiv,
      ``ManuscriptAudit.NodalProjectiveHOneExact.compactHOneEquiv,
      ``ManuscriptAudit.NodalProjectiveHOneExact.properSmoothHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
