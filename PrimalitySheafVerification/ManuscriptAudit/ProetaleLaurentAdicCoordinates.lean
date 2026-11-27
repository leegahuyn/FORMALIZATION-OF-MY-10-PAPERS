import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentCompatibleHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicReductionAllDegrees

/-! The ordinary compatible tower of actual native finite Laurent groups
has canonical adic coordinates after the coherent roots have been chosen. -/

namespace ManuscriptAudit.ProetaleLaurentAdicCoordinates

open AlgebraicGeometry CategoryTheory
open ProetaleLaurentCompatibleHOne (laurent cyclicToHOne cyclicToHOne_naturality)
open ProetaleAdicHOneDetection (finiteCoefficient compatibleHOne)
open ProetaleAdicReductionAllDegrees (nativeStep level_naturality)
open ProetaleDiscreteConstant (nativeResidueIso)
open ProetaleCohomologyIso (cohomologyIso)
open PadicResidueSystems (systems reduction padicRingEquiv compatible_of_successors)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

/-- The native cyclic group at level `n`, with its actual residue coefficients. -/
def levelEquiv (n : ℕ) : ZMod (ℓ ^ n) ≃+ Sheaf.H (finiteCoefficient (laurent K) ℓ n) 1 :=
  (cyclicToHOne K ℓ n).trans (cohomologyIso (X := laurent K) (nativeResidueIso (laurent K) ℓ n) 1)

theorem level_natural (n : ℕ) (x : ZMod (ℓ ^ (n + 1))) :
    nativeStep (laurent K) ℓ 1 n (levelEquiv K ℓ (n + 1) x) =
      levelEquiv K ℓ n (reduction ℓ (Nat.le_succ n) x) := by
  let e := cohomologyIso (X := laurent K) (nativeResidueIso (laurent K) ℓ n) 1
  calc
    _ = e (Sheaf.H.map (ProetaleLaurentCompatibleHOne.transition K ℓ n) 1
        (cyclicToHOne K ℓ (n + 1) x)) :=
      (level_naturality (laurent K) ℓ 1 n (cyclicToHOne K ℓ (n + 1) x)).symm
    _ = _ := congrArg e (cyclicToHOne_naturality K ℓ n x)

private def fromSystems :
    systems ℓ ≃+ compatibleHOne (laurent K) ℓ where
  toFun x := ⟨fun n ↦ levelEquiv K ℓ n (x.val n), fun n ↦ by
    change nativeStep (laurent K) ℓ 1 n (levelEquiv K ℓ (n + 1) (x.val (n + 1))) =
      levelEquiv K ℓ n (x.val n)
    rw [level_natural, x.property n (n + 1) (Nat.le_succ n)]⟩
  invFun x := ⟨fun n ↦ (levelEquiv K ℓ n).symm (x.val n),
    compatible_of_successors ℓ _ (fun n ↦ by
      apply (levelEquiv K ℓ n).injective
      change levelEquiv K ℓ n (reduction ℓ (Nat.le_succ n)
        ((levelEquiv K ℓ (n + 1)).symm (x.val (n + 1)))) =
          levelEquiv K ℓ n ((levelEquiv K ℓ n).symm (x.val n))
      rw [← level_natural, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      exact x.property n)⟩
  left_inv x := Subtype.ext (funext fun n ↦ (levelEquiv K ℓ n).symm_apply_apply _)
  right_inv x := Subtype.ext (funext fun n ↦ (levelEquiv K ℓ n).apply_symm_apply _)
  map_add' x y := Subtype.ext (funext fun n ↦ (levelEquiv K ℓ n).map_add _ _)

/-- Additive adic coordinates for the compatible finite native Laurent groups. -/
def compatibleEquiv : ℤ_[ℓ] ≃+ compatibleHOne (laurent K) ℓ :=
  (padicRingEquiv ℓ).toAddEquiv.trans (fromSystems K ℓ)

theorem compatibleEquiv_apply (x : ℤ_[ℓ]) (n : ℕ) :
    (compatibleEquiv K ℓ x).val n = levelEquiv K ℓ n (PadicInt.toZModPow n x) := rfl

end
end ManuscriptAudit.ProetaleLaurentAdicCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleLaurentAdicCoordinates.level_natural,
      ``ManuscriptAudit.ProetaleLaurentAdicCoordinates.compatibleEquiv,
      ``ManuscriptAudit.ProetaleLaurentAdicCoordinates.compatibleEquiv_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
