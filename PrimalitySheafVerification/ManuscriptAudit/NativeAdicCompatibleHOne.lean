import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne

/-! The actual native degree-one integral group maps bijectively
to its compatible finite native residue groups on the proper split
node and the proper cusp. The comparison is the actual reduction map. -/

namespace ManuscriptAudit.NativeAdicCompatibleHOne

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizedNode)
open CuspProperCompactification (projectiveCusp)
open NodalNativeAdicConductorReduction
open NodalNativeConductorHOne (boundary_injective boundary_surjective)
open ProetaleAdicHOneDetection (finiteCoefficient compatibleHOne reductionMap reductionMap_injective)
open PadicResidueSystems (padicRingEquiv systems compatible_of_successors)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section Node

variable (K : Type) [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveNode K

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private def labelEquivalence (n : ℕ) :
    ZMod (ℓ ^ n) ≃+ Sheaf.H (finiteCoefficient (X K) ℓ n) 1 :=
  AddEquiv.ofBijective (finiteLabel K h2 ℓ n)
    ⟨boundary_injective K h2 (ZMod (ℓ ^ n)),
      boundary_surjective K h2 (ZMod (ℓ ^ n))
        (NodalNormalizedProetaleHOne.residue_HOne_subsingleton K h2 ℓ n)⟩

include h2 in
/-- Every compatible tuple of actual native finite residue classes
on the proper split node is the reduction of its p-adic conductor label. -/
theorem node_reduction_surjective : Function.Surjective (reductionMap (X K) ℓ) := by
  intro x
  let t (n : ℕ) := (labelEquivalence K h2 ℓ n).symm (x.val n)
  have he (n : ℕ) : finiteLabel K h2 ℓ n (t n) = x.val n :=
    (labelEquivalence K h2 ℓ n).apply_symm_apply _
  have ht (n : ℕ) : PadicResidueSystems.reduction ℓ (Nat.le_succ n) (t (n + 1)) = t n := by
    apply (labelEquivalence K h2 ℓ n).injective
    change finiteLabel K h2 ℓ n (PadicResidueSystems.reduction ℓ (Nat.le_succ n) (t (n + 1))) =
      finiteLabel K h2 ℓ n (t n)
    rw [← finiteLabel_transition, he, he]
    exact x.property n
  let y : systems ℓ := ⟨t, compatible_of_successors ℓ t ht⟩
  let a := (padicRingEquiv ℓ).symm y
  have ha (n : ℕ) : PadicInt.toZModPow n a = t n :=
    congrArg (fun c : systems ℓ ↦ c.val n) ((padicRingEquiv ℓ).apply_symm_apply y)
  refine ⟨integralBoundary K h2 ℓ a, ?_⟩
  apply Subtype.ext
  funext n
  change Sheaf.H.map (reduction K ℓ n) 1 (integralBoundary K h2 ℓ a) = x.val n
  rw [integralBoundary_reduction, ha, he]

/-- The literal native integral comparison on the proper split node, in degree one. -/
def nodeReductionEquiv :
    (X K).EllAdicCohomology ℓ 1 ≃+ compatibleHOne (X K) ℓ :=
  AddEquiv.ofBijective (reductionMap (X K) ℓ)
    ⟨reductionMap_injective (X K) ℓ, node_reduction_surjective K h2 ℓ⟩

theorem nodeReductionEquiv_apply (x : (X K).EllAdicCohomology ℓ 1) :
    nodeReductionEquiv K h2 ℓ x = reductionMap (X K) ℓ x := rfl

end Node

section Trivial

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual comparison is also bijective on any scheme whose
native finite residue groups in degree one are all trivial. -/
def reductionEquivOfTrivialResidues
    (h : ∀ n : ℕ, Subsingleton (Sheaf.H (finiteCoefficient X ℓ n) 1)) :
    X.EllAdicCohomology ℓ 1 ≃+ compatibleHOne X ℓ :=
  AddEquiv.ofBijective (reductionMap X ℓ) ⟨reductionMap_injective X ℓ, by
    intro x
    refine ⟨0, ?_⟩
    apply Subtype.ext
    funext n
    exact (h n).elim _ _⟩

end Trivial

/-- The literal native integral comparison on the proper cusp, in degree one. -/
def cuspReductionEquiv (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    (projectiveCusp K).EllAdicCohomology ℓ 1 ≃+ compatibleHOne (projectiveCusp K) ℓ :=
  reductionEquivOfTrivialResidues (projectiveCusp K) ℓ
    (CuspNativeProetaleProperHOne.residue_HOne_subsingleton K ℓ)

end
end ManuscriptAudit.NativeAdicCompatibleHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAdicCompatibleHOne.node_reduction_surjective,
      ``ManuscriptAudit.NativeAdicCompatibleHOne.nodeReductionEquiv,
      ``ManuscriptAudit.NativeAdicCompatibleHOne.nodeReductionEquiv_apply,
      ``ManuscriptAudit.NativeAdicCompatibleHOne.reductionEquivOfTrivialResidues,
      ``ManuscriptAudit.NativeAdicCompatibleHOne.cuspReductionEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
