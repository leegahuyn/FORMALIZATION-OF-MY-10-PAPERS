import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicConductorReduction
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! Degree one of Mathlib's literal integral pro-étale coefficient
sheaf on the proper split node is one copy of the p-adic integers. -/

namespace ManuscriptAudit.NodalNativeAdicHOne

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizedNode)
open NodalNativeAdicConductorReduction
open NodalNativeConductorHOne (boundary_injective boundary_surjective)
open ProetaleAdicHOneDetection (finiteCoefficient reductionMap reductionMap_injective)
open PadicResidueSystems (padicRingEquiv systems compatible_of_successors)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveNode K

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private theorem finiteLabel_bijective (n : ℕ) : Function.Bijective (finiteLabel K h2 ℓ n) :=
  ⟨boundary_injective K h2 (ZMod (ℓ ^ n)),
    boundary_surjective K h2 (ZMod (ℓ ^ n))
      (NodalNormalizedProetaleHOne.residue_HOne_subsingleton K h2 ℓ n)⟩

private def finiteEquiv (n : ℕ) :
    ZMod (ℓ ^ n) ≃+ Sheaf.H (finiteCoefficient (X K) ℓ n) 1 :=
  AddEquiv.ofBijective (finiteLabel K h2 ℓ n) (finiteLabel_bijective K h2 ℓ n)

theorem integralBoundary_injective : Function.Injective (integralBoundary K h2 ℓ) := by
  intro a b h
  apply (padicRingEquiv ℓ).injective
  apply Subtype.ext
  funext n
  change PadicInt.toZModPow n a = PadicInt.toZModPow n b
  apply (finiteLabel_bijective K h2 ℓ n).1
  rw [← integralBoundary_reduction, ← integralBoundary_reduction, h]

theorem integralBoundary_surjective : Function.Surjective (integralBoundary K h2 ℓ) := by
  intro x
  let x' := reductionMap (X K) ℓ x
  let t (n : ℕ) := (finiteEquiv K h2 ℓ n).symm (x'.val n)
  have he (n : ℕ) : finiteLabel K h2 ℓ n (t n) = x'.val n :=
    (finiteEquiv K h2 ℓ n).apply_symm_apply _
  have ht (n : ℕ) : PadicResidueSystems.reduction ℓ (Nat.le_succ n) (t (n + 1)) = t n := by
    apply (finiteLabel_bijective K h2 ℓ n).1
    rw [← finiteLabel_transition, he, he]
    exact x'.property n
  let y : systems ℓ := ⟨t, compatible_of_successors ℓ t ht⟩
  let a := (padicRingEquiv ℓ).symm y
  have ha (n : ℕ) : PadicInt.toZModPow n a = t n :=
    congrArg (fun c : systems ℓ ↦ c.val n) ((padicRingEquiv ℓ).apply_symm_apply y)
  refine ⟨a, reductionMap_injective (X K) ℓ ?_⟩
  apply Subtype.ext
  funext n
  change Sheaf.H.map (reduction K ℓ n) 1 (integralBoundary K h2 ℓ a) = x'.val n
  rw [integralBoundary_reduction, ha, he]

/-- The actual Mathlib integral pro-étale H¹ is rank one over the
coefficient integers as an additive group, with its conductor generator. -/
def adicHOneEquiv : (X K).EllAdicCohomology ℓ 1 ≃+ ℤ_[ℓ] :=
  (AddEquiv.ofBijective (integralBoundary K h2 ℓ)
    ⟨integralBoundary_injective K h2 ℓ, integralBoundary_surjective K h2 ℓ⟩).symm

end
end ManuscriptAudit.NodalNativeAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeAdicHOne.integralBoundary_injective,
      ``ManuscriptAudit.NodalNativeAdicHOne.integralBoundary_surjective,
      ``ManuscriptAudit.NodalNativeAdicHOne.adicHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
