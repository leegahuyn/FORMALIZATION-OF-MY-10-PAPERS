import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOne

/-! The nonzero projective nodal class also gives a nonzero
compact-support class of the actual affine node. -/

namespace ManuscriptAudit.NodalCompactSupportHOne

open CategoryTheory

noncomputable section

/-- The actual affine node has nontrivial cyclic degree-one compactly
supported étale cohomology over a separably closed field of odd characteristic
or characteristic zero. -/
theorem nodalHcOne_nontrivial (K : Type) [Field K] [IsSepClosed K] (h2 : (2 : K) ≠ 0) :
    Nontrivial (nodalHc K (AddCommGrpCat.of (ZMod 2)) 1) := by
  let e := nodalHcOneProjectiveEquiv K (AddCommGrpCat.of (ZMod 2))
  obtain ⟨x, y, hxy⟩ := (NodalProjectiveHOne.projectiveNode_HOne_nontrivial K h2).exists_pair_ne
  exact ⟨⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective h)⟩⟩

end
end ManuscriptAudit.NodalCompactSupportHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalCompactSupportHOne.nodalHcOne_nontrivial
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
