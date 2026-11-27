import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.ProetaleTwoBranchKernel

/-! A binary separator on a native normalization chart lifts any
constant conductor label once the positive branch's label is fixed. -/

namespace ManuscriptAudit.ProetaleBranchBinaryLabelling

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps ProetaleTwoBranchKernel

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

abbrev Binary := ZMod 2
local instance binaryTopology : TopologicalSpace Binary := ⊥
local instance binaryDiscrete : DiscreteTopology Binary := ⟨rfl⟩

variable {N P X : Scheme.{0}} {p : N ⟶ X} {q : P ⟶ X}
  (b₀ b₁ : P ⟶ N) (h₀ : b₀ ≫ p = q) (h₁ : b₁ ≫ p = q)
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The positive branch on actual binary normalization functions. -/
abbrev positiveTrace : functionsOver Binary p ⟶ functionsOver Binary q :=
  restriction Binary b₀ h₀

/-- The actual ordered difference on binary normalization functions. -/
abbrev binaryDifference : functionsOver Binary p ⟶ functionsOver Binary q :=
  difference p q b₀ b₁ h₀ h₁ Binary

/-- Each chosen binary label may be relabelled by a fixed coefficient;
the other label is sent to zero. -/
def relabel {U : X.ProEt} (ε : Binary) (m : M)
    (s : (functionsOver Binary p).obj.obj (op U)) :
    (functionsOver M p).obj.obj (op U) :=
  let f : C(Binary, M) := ⟨fun t ↦ if t = ε then m else 0, continuous_of_discreteTopology⟩
  ⟨f.comp s.down⟩

/-- The relabelled section has the desired conductor difference. -/
theorem relabel_difference_const {U : X.ProEt} (ε : Binary) (m : M)
    (s : (functionsOver Binary p).obj.obj (op U))
    (hDiff : (binaryDifference b₀ b₁ h₀ h₁).hom.app (op U) s =
      ⟨ContinuousMap.const (↥(pullback U.hom q : Scheme.{0})) 1⟩)
    (hPos : (positiveTrace b₀ h₀).hom.app (op U) s =
      ⟨ContinuousMap.const (↥(pullback U.hom q : Scheme.{0})) ε⟩) :
    (difference p q b₀ b₁ h₀ h₁ M).hom.app (op U) (relabel M ε m s) =
      ⟨ContinuousMap.const (↥(pullback U.hom q : Scheme.{0})) m⟩ := by
  apply ULift.ext
  apply ContinuousMap.ext
  intro c
  let s' : C(pullback U.hom p, Binary) := s.down
  let x := s' (pullbackMap U.hom b₀ h₀ c)
  let y := s' (pullbackMap U.hom b₁ h₁ c)
  have hx : x = ε := congrArg (fun f : ULift.{1} (C(pullback U.hom q, Binary)) ↦ f.down c) hPos
  have hxy : x - y = 1 :=
    congrArg (fun f : ULift.{1} (C(pullback U.hom q, Binary)) ↦ f.down c) hDiff
  have hy : y ≠ ε := by
    intro h
    rw [hx, h, sub_self] at hxy
    exact zero_ne_one hxy
  change (if x = ε then m else 0) - (if y = ε then m else 0) = m
  rw [if_pos hx, if_neg hy, sub_zero]

end
end ManuscriptAudit.ProetaleBranchBinaryLabelling

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleBranchBinaryLabelling.relabel_difference_const
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
