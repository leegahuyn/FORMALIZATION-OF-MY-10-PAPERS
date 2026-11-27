import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAlgebraicallyClosed

/-! Actual weakly étale morphisms lift algebraically closed geometric
points through any chosen point of their scheme fiber. -/

namespace ManuscriptAudit.WeaklyEtaleGeometricPointLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Lift the actual geometric map through each chosen point of the weakly
étale morphism over its image. -/
theorem exists_lift {X S : Scheme.{u}} (f : X ⟶ S) [WeaklyEtale f]
    (s : Spec (CommRingCat.of K) ⟶ S) (x : X) (hx : f x = s (IsLocalRing.closedPoint K)) :
    ∃ l : Spec (CommRingCat.of K) ⟶ X, l ≫ f = s ∧ l (IsLocalRing.closedPoint K) = x := by
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := s) x
    (IsLocalRing.closedPoint K) hx
  obtain ⟨a, ha, hpoint⟩ :=
    WeaklyEtaleAlgebraicallyClosed.rationalSectionThrough K (pullback.snd f s) z
  refine ⟨a ≫ pullback.fst f s, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp]
  · rw [Scheme.Hom.comp_apply, hpoint, hz]

end
end ManuscriptAudit.WeaklyEtaleGeometricPointLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleGeometricPointLift.exists_lift
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
