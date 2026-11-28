import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull
import PrimalitySheafVerification.ManuscriptAudit.CoherentPrimitiveRoots

/-! Compatible cyclic coefficients and field roots have the same literal
power transitions when embedded into regular units on each affine chart. -/

namespace ManuscriptAudit.EtaleKummerCyclicCoordinates

open AlgebraicGeometry CategoryTheory Opposite
open KummerRelativeCoefficients (coefficientMap constantToRoots)
open KummerConstantCoefficients (coefficientGroup)
open CoherentPrimitiveRoots

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (l n : ℕ)

abbrev cyclicGroup := AddCommGrpCat.of (ZMod (l ^ n))

/-- Literal power transition between the étale coefficient roots. -/
def coefficientStep : coefficientGroup K (l ^ (n + 1)) ⟶ coefficientGroup K (l ^ n) :=
  AddCommGrpCat.ofHom (rootTransition K l n).toAdditive

abbrev reduction : cyclicGroup l (n + 1) ⟶ cyclicGroup l n :=
  AddCommGrpCat.ofHom (PadicResidueSystems.reduction l (Nat.le_succ n)).toAddMonoidHom

variable {K} {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))

abbrev label (d : ℕ) := constantToRoots k d ≫ KummerKernel.inclusion X d

/-- The actual labels in the regular unit presheaf preserve root powers. -/
theorem label_step :
    (Functor.const X.AffineEtaleᵒᵖ).map (coefficientStep K l n) ≫ label k (l ^ n) =
      label k (l ^ (n + 1)) ≫ KummerUnitsPresheaf.power X l := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  apply Additive.ext
  apply Units.ext
  let f := coefficientMap k U.unop
  let x : rootsOfUnity (l ^ (n + 1)) K := a.toMul
  change f ((x.val : K) ^ l) = f (x.val : K) ^ l
  exact map_pow f _ _

variable (K) [IsAlgClosed K] [Fact l.Prime] [NeZero (l : K)]

/-- A coherent primitive root identifies the literal cyclic object and
the literal roots-of-unity coefficient object in each degree. -/
def cyclicIso : cyclicGroup l n ≅ coefficientGroup K (l ^ n) :=
  (fromExponent K l n).toAdditive.toAddCommGrpIso

theorem cyclicIso_step :
    (cyclicIso K l (n + 1)).hom ≫ coefficientStep K l n =
      reduction l n ≫ (cyclicIso K l n).hom := by
  apply AddCommGrpCat.ext
  intro a
  apply Additive.ext
  exact fromExponent_transition K l n a

end

end ManuscriptAudit.EtaleKummerCyclicCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleKummerCyclicCoordinates.label_step,
      ``ManuscriptAudit.EtaleKummerCyclicCoordinates.cyclicIso_step] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
