import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoherentPrimitiveRoots
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerKernelTransition

/-! The actual coefficient embedding into regular units is compatible
with the power transition between successive cyclic levels. -/

namespace ManuscriptAudit.ProetaleKummerConstantTransition

open AlgebraicGeometry CategoryTheory Opposite
open CoherentPrimitiveRoots (rootTransition)
open ProetaleKummerPower (J G power power_eval)
open ProetaleKummerCoefficientMap (coefficientGroup coefficientMap constantToRoots)
open ProetaleKummerRoots (inclusion)
open ProetaleUnitSheaf (unitSheaf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (ℓ n : ℕ)

/-- Power on the actual lifted additive coefficient object. -/
def coefficientTransition : coefficientGroup K (ℓ ^ (n + 1)) ⟶ coefficientGroup K (ℓ ^ n) :=
  AddCommGrpCat.uliftFunctor.{1}.map (AddCommGrpCat.ofHom (rootTransition K ℓ n).toAdditive)

variable {K}
variable {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))

/-- The presheaf coefficient embedding into actual units. -/
abbrev label (d : ℕ) := constantToRoots k d ≫ inclusion X d

set_option maxHeartbeats 1000000 in
theorem label_transition :
    (Functor.const X.ProEtᵒᵖ).map (coefficientTransition K ℓ n) ≫ label k (ℓ ^ n) =
      label k (ℓ ^ (n + 1)) ≫ (power X ℓ).hom := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  change (inclusion X (ℓ ^ n)).app U ((constantToRoots k (ℓ ^ n)).app U
      (coefficientTransition K ℓ n a)) =
    (power X ℓ).hom.app U ((inclusion X (ℓ ^ (n + 1))).app U
      ((constantToRoots k (ℓ ^ (n + 1))).app U a))
  rw [power_eval]
  apply ULift.ext
  apply Additive.ext
  apply Units.ext
  let f := (coefficientMap k U.unop).hom
  let x : rootsOfUnity (ℓ ^ (n + 1)) K := a.down.toMul
  change f ((x.val : K) ^ ℓ) = f (x.val : K) ^ ℓ
  exact map_pow f _ _

end
end ManuscriptAudit.ProetaleKummerConstantTransition

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleKummerConstantTransition.label_transition
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
