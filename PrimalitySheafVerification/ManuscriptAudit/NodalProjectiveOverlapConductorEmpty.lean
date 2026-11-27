import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineOrigin
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocus

/-! The native overlap does not meet the affine nodal conductor. -/

namespace ManuscriptAudit.NodalProjectiveOverlapConductorEmpty

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProperYChart (chartOpen)
open NodalAffineOrigin (originMap originPoint)
open NodalSmoothLocus (nodePoint smooth_pieces_cover_complement)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

abbrev overlapMap := pullback.fst (affineOpen K) (chartOpen K)
abbrev overlap := Scheme.Etale.mk (overlapMap K)

private theorem pullback_no_points {S U V : Scheme.{0}} (f : U ⟶ S) (g : V ⟶ S)
    (h : ∀ (x : U) (y : V), f x ≠ g y) : IsEmpty (pullback f g : Scheme.{0}) := by
  refine ⟨fun z ↦ h (pullback.fst f g z) (pullback.snd f g z) ?_⟩
  exact congrArg (fun m : pullback f g ⟶ S ↦ m z) pullback.condition

set_option maxHeartbeats 350000 in
/-- The actual overlap of the two standard charts has empty conductor pullback. -/
theorem overlap_conductor_isEmpty :
    IsEmpty (pullback (overlapMap K) (originMap K) : Scheme.{0}) := by
  apply pullback_no_points
  intro p q hp
  have hq : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hOrigin : overlapMap K p = originPoint K :=
    hp.trans (congrArg (originMap K) hq)
  have hSquare : chartOpen K (pullback.snd (affineOpen K) (chartOpen K) p) =
      affineOpen K (overlapMap K p) :=
    congrArg (fun m : pullback (affineOpen K) (chartOpen K) ⟶ projectiveNode K ↦ m p)
      (pullback.condition (f := affineOpen K) (g := chartOpen K)).symm
  have hChart : nodePoint K ∈ Set.range (chartOpen K) :=
    ⟨_, hSquare.trans (congrArg (affineOpen K) hOrigin)⟩
  have hOut : nodePoint K ∈ ({nodePoint K} : Set (projectiveNode K))ᶜ :=
    (smooth_pieces_cover_complement K).le (Or.inr hChart)
  exact hOut (Set.mem_singleton _)

end
end ManuscriptAudit.NodalProjectiveOverlapConductorEmpty

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveOverlapConductorEmpty.overlap_conductor_isEmpty] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
