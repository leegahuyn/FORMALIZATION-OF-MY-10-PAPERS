import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerConstantTransition

/-! The actual cyclic coefficient objects identify coherently with
constant algebraic roots of unity at all invertible prime-power orders. -/

namespace ManuscriptAudit.ProetaleKummerCyclicCoordinates

open CategoryTheory
open CoherentPrimitiveRoots (fromExponent fromExponent_transition)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleKummerConstantTransition (coefficientTransition)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

abbrev cyclicGroup (n : ℕ) := AddCommGrpCat.of (ULift.{1} (ZMod (ℓ ^ n)))

/-- The actual lifted additive cyclic coefficient isomorphism. -/
def cyclicIso (n : ℕ) : cyclicGroup ℓ n ≅ coefficientGroup K (ℓ ^ n) :=
  (AddEquiv.ulift.trans ((fromExponent K ℓ n).toAdditive.trans AddEquiv.ulift.symm)).toAddCommGrpIso

abbrev reduction (n : ℕ) : cyclicGroup ℓ (n + 1) ⟶ cyclicGroup ℓ n :=
  AddCommGrpCat.uliftFunctor.{1}.map
    (AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom)

theorem cyclicIso_naturality (n : ℕ) :
    (cyclicIso K ℓ (n + 1)).hom ≫ coefficientTransition K ℓ n =
      reduction ℓ n ≫ (cyclicIso K ℓ n).hom := by
  apply AddCommGrpCat.ext
  intro a
  apply ULift.ext
  apply Additive.ext
  exact fromExponent_transition K ℓ n a.down

end
end ManuscriptAudit.ProetaleKummerCyclicCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleKummerCyclicCoordinates.cyclicIso_naturality
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
