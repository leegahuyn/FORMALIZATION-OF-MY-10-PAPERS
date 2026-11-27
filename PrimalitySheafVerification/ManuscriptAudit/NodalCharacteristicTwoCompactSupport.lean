import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoProjective
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHigher

/-! In characteristic two the actual compact-support groups of the two
affine equations identify through their isomorphic proper closures. -/

namespace ManuscriptAudit.NodalCharacteristicTwoCompactSupport

open AlgebraicGeometry CategoryTheory
open NodalCharacteristicTwoProjective (projectiveIso projective_cyclic_HOne_subsingleton)
open NodalCompactSupportHOne (nodalHc nodalHcSuccProjectiveEquiv nodalHcOneProjectiveEquiv)
open CuspCompactSupportSequence (cuspHc cuspHcSuccProjectiveEquiv)
open SmallEtaleEquivalenceCohomology (schemeIsoCohomologyEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

section PositiveDegrees

variable (K : Type u) [Field K] [IsSepClosed K] [CharP K 2]

/-- With any abelian coefficient group, the actual compact-support
cohomology of the two affine schemes agrees in every positive degree. -/
def affineHcSuccEquiv (A : AddCommGrpCat.{u}) (n : ℕ) :
    nodalHc K A (n + 1) ≃+ cuspHc K A (n + 1) :=
  (nodalHcSuccProjectiveEquiv K A n).trans
    ((schemeIsoCohomologyEquiv (projectiveIso K) A (n + 1)).trans
      (cuspHcSuccProjectiveEquiv K A n).symm)

end PositiveDegrees

section DegreeOne

variable (K : Type) [Field K] [IsAlgClosed K] [CharP K 2]

/-- In the geometric characteristic-two fiber, degree-one compact
support vanishes for every invertible cyclic coefficient order. -/
theorem affineHcOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (nodalHc K (AddCommGrpCat.of (ZMod d)) 1) := by
  let e := nodalHcOneProjectiveEquiv K (AddCommGrpCat.of (ZMod d))
  have h := projective_cyclic_HOne_subsingleton K d
  exact ⟨fun a b => e.injective (h.elim _ _)⟩

end DegreeOne

end
end ManuscriptAudit.NodalCharacteristicTwoCompactSupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwoCompactSupport.affineHcSuccEquiv,
      ``ManuscriptAudit.NodalCharacteristicTwoCompactSupport.affineHcOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
