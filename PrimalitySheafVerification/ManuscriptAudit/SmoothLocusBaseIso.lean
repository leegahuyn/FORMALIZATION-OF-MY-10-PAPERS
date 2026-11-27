import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SmoothLocusUnderIso

/-! The relative smooth open is invariant under an isomorphism
of the coefficient scheme, as well as of the source scheme. -/

namespace ManuscriptAudit.SmoothLocusBaseIso

open AlgebraicGeometry CategoryTheory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y S T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  (i : S ≅ T)

/-- Postcomposing with a base isomorphism preserves the actual smooth open. -/
theorem smoothLocus_postcomp :
    (f ≫ i.hom).smoothLocus = f.smoothLocus := by
  ext x
  change ((f ≫ i.hom).stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (i.hom.stalkMap (f x)) (f.stalkMap x)

/-- A commutative square with source and base isomorphisms identifies
the actual relative smooth schemes. -/
def iso (e : X ≅ Y) (g : Y ⟶ T) [LocallyOfFinitePresentation g]
    (h : e.hom ≫ g = f ≫ i.hom) :
    f.smoothLocus.toScheme ≅ g.smoothLocus.toScheme :=
  eqToIso (congrArg (fun U : X.Opens => U.toScheme) (smoothLocus_postcomp f i).symm) ≪≫
    SmoothLocusUnderIso.iso e (f ≫ i.hom) g h

end
end ManuscriptAudit.SmoothLocusBaseIso

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmoothLocusBaseIso.smoothLocus_postcomp,
      ``ManuscriptAudit.SmoothLocusBaseIso.iso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
