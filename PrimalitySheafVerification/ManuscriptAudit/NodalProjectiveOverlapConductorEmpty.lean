import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.Etale
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineOrigin
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocus

/-! The native overlap does not meet the affine nodal conductor. -/

namespace ManuscriptAudit.NodalProjectiveOverlapConductorEmpty

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineOpen)
open NodalProperYChart (chartOpen)
open NodalAffineOrigin (originMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private theorem overlap_avoids_constant_point {X U V S : Scheme.{u}} [Subsingleton S]
    (j : U ⟶ X) (k : V ⟶ X) (o : S ⟶ U) (s₀ : S)
    (h : j (o s₀) ∉ Set.range k) :
    IsEmpty (pullback (pullback.fst j k) o : Scheme.{u}) := by
  constructor
  intro z
  let m := pullback.fst j k
  let x := pullback.fst m o z
  let y := pullback.snd m o z
  have h₁ : j (m x) = k (pullback.snd j k x) :=
    congrArg (fun a : pullback j k ⟶ X ↦ a x) (pullback.condition (f := j) (g := k))
  have h₂ : m x = o y :=
    congrArg (fun a : pullback m o ⟶ U ↦ a z) (pullback.condition (f := m) (g := o))
  have hy : y = s₀ := Subsingleton.elim _ _
  exact h ⟨_, h₁.symm.trans (congrArg j (h₂.trans (congrArg o hy)))⟩

variable (K : Type) [Field K]

abbrev overlapMap := pullback.fst (affineOpen K) (chartOpen K)
abbrev overlap := Scheme.Etale.mk (overlapMap K)

/-- Pulling the actual rational conductor point back to the actual chart overlap gives the empty scheme. -/
theorem overlap_conductor_isEmpty :
    IsEmpty (pullback (overlapMap K) (originMap K) : Scheme.{0}) :=
  overlap_avoids_constant_point (affineOpen K) (chartOpen K) (originMap K)
    (IsLocalRing.closedPoint K) (NodalSmoothLocus.nodePoint_not_in_chartOpen K)

end
end ManuscriptAudit.NodalProjectiveOverlapConductorEmpty

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProjectiveOverlapConductorEmpty.overlap_conductor_isEmpty
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
