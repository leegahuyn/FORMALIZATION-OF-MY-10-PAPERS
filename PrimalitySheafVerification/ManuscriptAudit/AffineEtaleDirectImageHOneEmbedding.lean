import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunction
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleInverseImageConstants

/-! The genuine cohomology map from the direct image of an abelian étale
sheaf to the source scheme is injective in degree one for affine schemes. -/

namespace ManuscriptAudit.AffineEtaleDirectImageHOneEmbedding

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u

/-- Native direct-image H¹ embeds additively into the actual source H¹. -/
theorem HOne_embedding (R S : CommRingCat.{u}) (f : Spec S ⟶ Spec R)
    (F : Sheaf (Spec S).smallEtaleTopology AddCommGrpCat.{u}) :
    ∃ g : Sheaf.H ((SmallEtaleBaseChange.directImage f AddCommGrpCat.{u}).obj F) 1 →+
      Sheaf.H F 1, Function.Injective g := by
  let X := Spec S
  let Y := Spec R
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let B := Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  letI : IsGrothendieckAbelian.{u} B :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology Y AddCommGrpCat.{u}
  letI : EnoughInjectives B := IsGrothendieckAbelian.enoughInjectives.{u} (C := B)
  obtain ⟨L, ⟨adj⟩, hL⟩ := AffineEtaleMorphism.fullDirectImage_hasLeftExactLeftAdjoint R S f
  letI : PreservesFiniteLimits L := hL
  letI : L.IsLeftAdjoint := adj.isLeftAdjoint
  letI : PreservesFiniteColimits L := inferInstance
  letI : L.Additive := L.additive_of_preserves_binary_products
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let ZY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj Z
  let c := SmallEtaleInverseImageConstants.inverseImageConstantObjectIso f AddCommGrpCat.{u} adj Z
  let a := ExtOneAdjunction.map adj ZY F
  let e := (((extFunctor (C := C) 1).mapIso c.symm.op).app F).addCommGroupIsoToAddEquiv
  exact ⟨e.toAddMonoidHom.comp a, e.injective.comp (ExtOneAdjunction.map_injective adj ZY F)⟩

end
end ManuscriptAudit.AffineEtaleDirectImageHOneEmbedding

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleDirectImageHOneEmbedding.HOne_embedding
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
