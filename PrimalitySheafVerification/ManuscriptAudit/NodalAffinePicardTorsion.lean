import Lean.Util.CollectAxioms
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import PrimalitySheafVerification.ManuscriptAudit.NodalAffinePicard

/-! The actual algebraic Picard group of the split nodal affine curve has
exactly d elements killed by d over an algebraically closed field of
characteristic not dividing d. -/

namespace ManuscriptAudit.NodalAffinePicardTorsion

open NodalBranchLines NodalAffinePicard

noncomputable section
variable (K : Type*) [Field K]

def killedBy (d : ℕ) : Subgroup (CommRing.Pic (A K)) :=
  (powMonoidHom d).ker

/-- Transport the actual d-torsion in the nodal Picard group to
coefficient roots of unity. -/
def killedByEquiv (h2 : (2 : K) ≠ 0) (d : ℕ) :
    rootsOfUnity d K ≃* killedBy K d where
  toFun u := ⟨picardEquiv K h2 u.val, by
    change (picardEquiv K h2 u.val) ^ d = 1
    have hu : (u.val : Kˣ) ^ d = 1 := u.prop
    rw [← map_pow, hu, map_one]⟩
  invFun p := ⟨(picardEquiv K h2).symm p.val, by
    change ((picardEquiv K h2).symm p.val) ^ d = 1
    have hp : p.val ^ d = 1 := p.prop
    rw [← map_pow, hp, map_one]⟩
  left_inv u := Subtype.ext ((picardEquiv K h2).symm_apply_apply u.val)
  right_inv p := Subtype.ext ((picardEquiv K h2).apply_symm_apply p.val)
  map_mul' u v := Subtype.ext ((picardEquiv K h2).map_mul u.val v.val)

/-- Exact number of d-torsion line bundles on the actual affine node. -/
theorem killedBy_card [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (d : ℕ)
    [NeZero d] [NeZero (d : K)] :
    Nat.card (killedBy K d) = d :=
  (Nat.card_congr (killedByEquiv K h2 d).symm.toEquiv).trans
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity K d)

end
end ManuscriptAudit.NodalAffinePicardTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAffinePicardTorsion.killedByEquiv,
      ``ManuscriptAudit.NodalAffinePicardTorsion.killedBy_card] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
