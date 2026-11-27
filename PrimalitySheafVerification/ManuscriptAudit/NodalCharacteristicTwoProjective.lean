import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoChart
import PrimalitySheafVerification.ManuscriptAudit.IntegralOddPrimeFibers
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAbsoluteHOne

/-! The actual characteristic-two projective node model is the proper
cusp. The projective-plane automorphism transports the two schematic
closures of the checked affine embeddings. -/

namespace ManuscriptAudit.NodalCharacteristicTwoProjective

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp cuspInPlane)
open NodalProjectiveClosure (projectiveNode nodeInPlane)
open NodalCharacteristicTwoPlane (planeChange planeChange_comp planeIso)
open NodalCharacteristicTwoAffine (affineIso)
open NodalCharacteristicTwoChart (affine_square)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

section AnyField

universe u
variable (K : Type u) [Field K] [CharP K 2]

private abbrev movedNode :=
  (nodeInPlane K).imageι ≫ planeChange K

private theorem closed_embedding_kernel :
    (movedNode K).ker = (cuspInPlane K).imageι.ker := by
  have hAffine : (affineIso K).hom ≫ (nodeInPlane K ≫ planeChange K) = cuspInPlane K := by
    rw [← Category.assoc, affine_square K, Category.assoc, planeChange_comp K, Category.comp_id]
  calc
    _ = (nodeInPlane K ≫ planeChange K).ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_comp]
      change ((nodeInPlane K).ker.subschemeι.ker).map (planeChange K) =
        (nodeInPlane K).ker.map (planeChange K)
      rw [Scheme.IdealSheafData.ker_subschemeι]
    _ = ((affineIso K).hom ≫ (nodeInPlane K ≫ planeChange K)).ker :=
      (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (cuspInPlane K).ker := by rw [hAffine]
    _ = _ := (Scheme.IdealSheafData.ker_subschemeι _).symm

/-- Isomorphism of the actual proper schematic closures. -/
def projectiveIso : projectiveNode K ≅ projectiveCusp K := by
  letI : IsIso (planeChange K) := (planeIso K).isIso_hom
  haveI : IsClosedImmersion (movedNode K) := by
    unfold movedNode
    infer_instance
  let h := (closed_embedding_kernel K).symm
  let m := IsClosedImmersion.lift (cuspInPlane K).imageι (movedNode K) h.le
  letI : IsIso m := IsClosedImmersion.isIso_lift _ _ h
  exact asIso m

theorem projectiveIso_in_plane :
    (projectiveIso K).hom ≫ (cuspInPlane K).imageι = movedNode K := by
  unfold projectiveIso
  exact IsClosedImmersion.lift_fac _ _ _

end AnyField

/-- The canonical proper nodal-equation fiber at (2) is the proper cusp. -/
def canonicalProperFiberIso :
    IntegralOddPrimeFibers.nodalFiber 2 ≅ projectiveCusp (ZMod 2) :=
  IntegralOddPrimeFibers.nodeIso 2 ≪≫ projectiveIso (ZMod 2)

section GeometricCoefficients

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K] [CharP K 2]

/-- The degree-one small étale cohomology of the proper characteristic-two
fiber vanishes for every invertible cyclic coefficient order. -/
theorem projective_cyclic_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (projectiveNode K).smallEtaleTopology
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 1) := by
  let e := SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
    (projectiveIso K) (AddCommGrpCat.of (ZMod d)) 1
  have h := CuspCompactSupportAbsoluteHOne.projectiveCusp_HOne_subsingleton K 2 d
  exact ⟨fun a b => e.injective (h.elim _ _)⟩

end GeometricCoefficients

end
end ManuscriptAudit.NodalCharacteristicTwoProjective

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwoProjective.projectiveIso,
      ``ManuscriptAudit.NodalCharacteristicTwoProjective.projectiveIso_in_plane,
      ``ManuscriptAudit.NodalCharacteristicTwoProjective.canonicalProperFiberIso,
      ``ManuscriptAudit.NodalCharacteristicTwoProjective.projective_cyclic_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
