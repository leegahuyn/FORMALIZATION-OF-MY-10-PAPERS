import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ExactFunctorExtAdjunction
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleInverseImageConstants
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero

/-! For affine schemes with exact actual étale direct image, ordinary cohomology is unchanged by pushforward. -/

namespace ManuscriptAudit.AffineEtaleExactDirectImageCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{u}

variable (R S : CommRingCat.{u}) (f : Spec S ⟶ Spec R)

/-- If native direct image preserves epimorphisms, the exact adjunction identifies cohomology in all degrees. -/
def cohomologyEquiv
    [(SmallEtaleBaseChange.directImage f A.{u}).PreservesEpimorphisms]
    (F : Sheaf (Spec S).smallEtaleTopology A.{u}) (n : ℕ) :
    Sheaf.H ((SmallEtaleBaseChange.directImage f A.{u}).obj F) n ≃+ Sheaf.H F n := by
  let X := Spec S
  let Y := Spec R
  let C := Sheaf X.smallEtaleTopology A.{u}
  let G := SmallEtaleBaseChange.directImage f A.{u}
  let h := AffineEtaleMorphism.fullDirectImage_hasLeftExactLeftAdjoint R S f
  let L := Classical.choose h
  let adj : L ⊣ G := Classical.choice (Classical.choose_spec h).1
  letI : PreservesFiniteLimits L := (Classical.choose_spec h).2
  letI : L.IsLeftAdjoint := adj.isLeftAdjoint
  letI : PreservesFiniteColimits L := inferInstance
  letI : L.Additive := L.additive_of_preserves_binary_products
  letI : G.IsRightAdjoint := adj.isRightAdjoint
  letI : PreservesFiniteLimits G := inferInstance
  letI : G.Additive := G.additive_of_preserves_binary_products
  letI : G.PreservesEpimorphisms :=
    inferInstanceAs ((SmallEtaleBaseChange.directImage f A.{u}).PreservesEpimorphisms)
  letI : ∀ {B D : C} (g : B ⟶ D), PreservesLimit (parallelPair g 0) G :=
    fun _ ↦ inferInstance
  letI : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
  letI : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let ZY := (constantSheaf Y.smallEtaleTopology A.{u}).obj Z
  let c := SmallEtaleInverseImageConstants.inverseImageConstantObjectIso f A.{u} adj Z
  let e := (ExactFunctorDerivedAdjunction.extAdjunction adj ZY F n).symm
  let d := (((extFunctor (C := C) n).mapIso c.symm.op).app F).addCommGroupIsoToAddEquiv
  exact e.trans d

end
end ManuscriptAudit.AffineEtaleExactDirectImageCohomology

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleExactDirectImageCohomology.cohomologyEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
