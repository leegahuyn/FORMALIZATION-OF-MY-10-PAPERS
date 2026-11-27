import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineStoneHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHOneDetection

/-! The actual integral adic H¹ vanishes on an affine weakly étale scheme
over an algebraically closed field. -/

namespace ManuscriptAudit.ProetaleAffineStoneAdicHOne

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (spectrum)
open ProetaleAdicHOneDetection (finiteCoefficient reductionMap reductionMap_injective)

noncomputable section

variable {K A : Type} [Field K] [IsAlgClosed K] [CommRing A]
    (c : spectrum A ⟶ Spec (CommRingCat.of K)) [WeaklyEtale c]
    (ℓ : ℕ) [Fact ℓ.Prime]

local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- Every finite reduction has zero actual pro-étale H¹. -/
theorem residue_HOne_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (spectrum A) ℓ n) 1) := by
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime ℓ).ne_zero⟩
  exact ProetaleAffineStoneHOne.HOne_subsingleton (M := ZMod (ℓ ^ n)) c

/-- Coherent residue detection forces the actual adic degree-one class to vanish. -/
theorem HOne_subsingleton : Subsingleton ((spectrum A).EllAdicCohomology ℓ 1) := by
  letI (n : ℕ) : Subsingleton (Sheaf.H (finiteCoefficient (spectrum A) ℓ n) 1) :=
    residue_HOne_subsingleton c ℓ n
  refine ⟨fun x y ↦ reductionMap_injective (spectrum A) ℓ ?_⟩
  apply Subtype.ext
  funext n
  exact Subsingleton.elim _ _

end
end ManuscriptAudit.ProetaleAffineStoneAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineStoneAdicHOne.residue_HOne_subsingleton,
      ``ManuscriptAudit.ProetaleAffineStoneAdicHOne.HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
