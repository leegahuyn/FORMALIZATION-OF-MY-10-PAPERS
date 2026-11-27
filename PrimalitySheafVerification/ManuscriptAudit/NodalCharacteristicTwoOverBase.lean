import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoProjective
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveFiberDimension

/-! The characteristic-two isomorphism of the two projective
closures is an isomorphism over the coefficient field. Its
restriction to the dense affine chart is the checked algebra map. -/

namespace ManuscriptAudit.NodalCharacteristicTwoOverBase

open AlgebraicGeometry CategoryTheory
open NodalCharacteristicTwoPlane (planeChange planeChange_comp)
open NodalCharacteristicTwoAffine (affineIso coordinateEquiv)
open NodalCharacteristicTwoChart (affine_square)
open NodalCharacteristicTwoProjective (projectiveIso projectiveIso_in_plane canonicalProperFiberIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

private theorem ext_to_spec_on_dominant {U X : Scheme.{0}} {K : Type} [CommRing K]
    (j : U ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    {f g : X ⟶ Spec (CommRingCat.of K)} (h : j ≫ f = j ≫ g) : f = g := by
  have hMap : f.appTop ≫ j.appTop = g.appTop ≫ j.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg (fun v : U ⟶ Spec (CommRingCat.of K) => v.appTop) h
  have hTop : f.appTop = g.appTop := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply j.app_injective ⊤
    exact congrArg (fun m : Γ(Spec (CommRingCat.of K), ⊤) ⟶ Γ(U, ⊤) => m.hom a) hMap
  apply ext_to_Spec
  rw [Scheme.Γ_map_op, Scheme.Γ_map_op, hTop]

section AnyField

variable (K : Type) [Field K] [CharP K 2]

open NodalProjectiveClosure (nodeInPlane projectiveNode projectiveNodeToBase)
open CuspProperCompactification (cuspInPlane projectiveCuspToBase)

private abbrev affineNodeOpen := NodalProjectiveClosure.affineOpen K
private abbrev affineCuspOpen := CuspProperCompactification.affineOpen K

/-- On the dense affine open, the projective isomorphism is the
explicit characteristic-two coordinate substitution. -/
theorem affine_square_on_closures :
    affineNodeOpen K ≫ (projectiveIso K).hom = (affineIso K).inv ≫ affineCuspOpen K := by
  let i := (cuspInPlane K).imageι
  have hIso : (projectiveIso K).hom ≫ i =
      (nodeInPlane K).imageι ≫ planeChange K := projectiveIso_in_plane K
  have hNode : affineNodeOpen K ≫ (nodeInPlane K).imageι = nodeInPlane K :=
    Scheme.Hom.toImage_imageι _
  have hCusp : affineCuspOpen K ≫ i = cuspInPlane K := Scheme.Hom.toImage_imageι _
  have hAff : (affineIso K).hom ≫ (nodeInPlane K ≫ planeChange K) = cuspInPlane K := by
    rw [← Category.assoc, affine_square K, Category.assoc, planeChange_comp K, Category.comp_id]
  apply (cancel_mono i).mp
  calc
    _ = affineNodeOpen K ≫ ((nodeInPlane K).imageι ≫ planeChange K) := by
      rw [Category.assoc, hIso]
    _ = nodeInPlane K ≫ planeChange K := by rw [← Category.assoc, hNode]
    _ = (affineIso K).inv ≫ cuspInPlane K := by
      symm
      rw [← hAff, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = _ := by rw [Category.assoc, hCusp]

private theorem inverseAffine_over :
    (affineIso K).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (CuspPunctured.CuspSubalgebra K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (NodalConductor.coordinates K))) := by
  change Spec.map (CommRingCat.ofHom (coordinateEquiv K).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (CuspPunctured.CuspSubalgebra K))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (coordinateEquiv K).symm.commutes

/-- The whole projective isomorphism respects the structure maps to Spec K. -/
theorem projectiveIso_over :
    (projectiveIso K).hom ≫ projectiveCuspToBase K = projectiveNodeToBase K := by
  letI : IsIntegral (projectiveNode K) := NodalProjectiveFiberDimension.projective_integral K
  letI : IsDominant (affineNodeOpen K) := NodalProjectiveClosure.affineOpen_isDominant K
  letI : IsSchemeTheoreticallyDominant (affineNodeOpen K) :=
    IsSchemeTheoreticallyDominant.of_isDominant (affineNodeOpen K)
  letI : QuasiCompact (nodeInPlane K) := quasiCompact_of_compactSpace _
  letI : QuasiCompact (affineNodeOpen K) :=
    inferInstanceAs (QuasiCompact (nodeInPlane K).toImage)
  apply ext_to_spec_on_dominant (affineNodeOpen K)
  rw [← Category.assoc, affine_square_on_closures K, Category.assoc,
    CuspProperCompactification.affineOpen_toBase K, NodalProjectiveClosure.affineOpen_toBase K]
  exact inverseAffine_over K

end AnyField

open IntegralOddPrimeFibers (nodeToResidue)
open IntPrimeResidueFiber (canonicalFiberIso canonicalFiberIso_over residueSpecIso)

private theorem coefficient_fiber_iso_inv_over :
    (canonicalFiberIso 2 (NodalIntegralGluing.toBase ℤ)).inv ≫
        IntegralNodalArithmeticBump.fiberToBase (ZMod 2) =
      nodeToResidue 2 ≫ (residueSpecIso 2).inv := by
  let e := canonicalFiberIso 2 (NodalIntegralGluing.toBase ℤ)
  let i := residueSpecIso 2
  have h : e.hom ≫ nodeToResidue 2 =
      IntegralNodalArithmeticBump.fiberToBase (ZMod 2) ≫ i.hom :=
    canonicalFiberIso_over 2 (NodalIntegralGluing.toBase ℤ)
  apply (cancel_mono i.hom).mp
  change (e.inv ≫ IntegralNodalArithmeticBump.fiberToBase (ZMod 2)) ≫ i.hom =
    (nodeToResidue 2 ≫ i.inv) ≫ i.hom
  rw [Category.assoc, ← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual canonical proper fiber at (2) is the proper cusp
as a scheme over its canonical residue field. -/
theorem canonicalProperFiberIso_over :
    canonicalProperFiberIso.hom ≫ CuspProperCompactification.projectiveCuspToBase (ZMod 2) =
      nodeToResidue 2 ≫ (residueSpecIso 2).inv := by
  unfold canonicalProperFiberIso IntegralOddPrimeFibers.nodeIso
  simp only [Iso.trans_hom, Category.assoc, projectiveIso_over,
    IntegralNodalArithmeticBump.fiberIso_over]
  exact coefficient_fiber_iso_inv_over

end
end ManuscriptAudit.NodalCharacteristicTwoOverBase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwoOverBase.affine_square_on_closures,
      ``ManuscriptAudit.NodalCharacteristicTwoOverBase.projectiveIso_over,
      ``ManuscriptAudit.NodalCharacteristicTwoOverBase.canonicalProperFiberIso_over] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
