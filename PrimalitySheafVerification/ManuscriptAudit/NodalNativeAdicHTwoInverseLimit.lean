import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicMilnorPositive

/-! The native proper node also has unique lifts of its compatible finite
degree-two classes, using its actual conductor classes in degree one. -/

namespace ManuscriptAudit.NodalNativeAdicHTwoInverseLimit

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalNativeAdicConductorReduction
open NodalNativeConductorHOne (boundary_surjective)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (nativeStep nativeCompatible)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

local instance (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

theorem residue_step_surjective (n : ℕ) :
    Function.Surjective (nativeStep (projectiveNode K) ℓ 1 n) := by
  intro u
  obtain ⟨a, ha⟩ := boundary_surjective K h2 (ZMod (ℓ^n))
    (NodalNormalizedProetaleHOne.residue_HOne_subsingleton K h2 ℓ n) u
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime ℓ).ne_zero⟩
  let b : ZMod (ℓ ^ (n+1)) := a.val
  have hb : PadicResidueSystems.reduction ℓ (Nat.le_succ n) b = a := by
    change PadicResidueSystems.reduction ℓ (Nat.le_succ n) (a.val : ZMod (ℓ^(n+1))) = a
    rw [map_natCast, ZMod.natCast_zmod_val]
  refine ⟨finiteLabel K h2 ℓ (n+1) b, ?_⟩
  change Sheaf.H.map (transition K ℓ n) 1 (finiteLabel K h2 ℓ (n+1) b) = u
  rw [finiteLabel_transition, hb]
  exact ha

/-- The actual native proper node's adic degree-two group is the inverse limit
of its finite level groups. -/
def reductionEquiv : (projectiveNode K).EllAdicCohomology ℓ 2 ≃+
    nativeCompatible (projectiveNode K) ℓ 2 :=
  ProetaleAdicMilnorPositive.reductionEquiv (projectiveNode K) ℓ 0
    (residue_step_surjective K h2 ℓ)

end
end ManuscriptAudit.NodalNativeAdicHTwoInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeAdicHTwoInverseLimit.residue_step_surjective,
      ``ManuscriptAudit.NodalNativeAdicHTwoInverseLimit.reductionEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
