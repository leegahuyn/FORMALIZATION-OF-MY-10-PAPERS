import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunction
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitDimensionShift
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleInverseImageConstants

/-!
# Comparing generic-unit cohomology to the fraction field

Both sides shift to degree one with the same native unit resolution.
The exact inverse image gives the injective Ext¹ comparison and sends
the constant source of the cohomology to the actual constant sheaf.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open KummerUnitsSheaf SmallEtaleBaseChange

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (A F : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field F]
  [Algebra A F] [IsFractionRing A F]

private abbrev X := Spec (CommRingCat.of A)
private abbrev Y := Spec (CommRingCat.of F)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev D := directImage (j A F) AddCommGrpCat.{0}

set_option maxHeartbeats 3600000 in
/-- Degree two of the actual generic-unit direct image embeds in degree
two of the actual unit sheaf on the fraction field. -/
def genericImageHTwoEmbedding :
    {m : Sheaf.H (genericUnitImage A F) 2 →+
        Sheaf.H (fullCoordinateUnitSheaf (Y F)) 2 // Function.Injective m} := by
  let C₀ := Sheaf (X A).smallEtaleTopology AddCommGrpCat.{0}
  let C₁ := Sheaf (Y F).smallEtaleTopology AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C₀ :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology (X A) AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C₁ :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology (Y F) AddCommGrpCat.{0}
  letI : EnoughInjectives C₀ := IsGrothendieckAbelian.enoughInjectives.{0} (C := C₀)
  letI : EnoughInjectives C₁ := IsGrothendieckAbelian.enoughInjectives.{0} (C := C₁)
  let h := AffineEtaleMorphism.fullDirectImage_hasLeftExactLeftAdjoint
    (CommRingCat.of A) (CommRingCat.of F) (j A F)
  let L := Classical.choose h
  let adj : L ⊣ D A F := Classical.choice (Classical.choose_spec h).1
  letI : PreservesFiniteLimits L := (Classical.choose_spec h).2
  letI : L.IsLeftAdjoint := adj.isLeftAdjoint
  letI : PreservesFiniteColimits L := inferInstance
  letI : L.Additive := L.additive_of_preserves_binary_products
  let G := fullCoordinateUnitSheaf (Y F)
  let i : G ⟶ Injective.under G := Injective.ι G
  letI : Mono i := inferInstanceAs (Mono (Injective.ι G))
  let Q := cokernel i
  let S := ShortComplex.cokernelSequence i
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i) (inferInstanceAs (Mono i))
    (inferInstanceAs (Epi (cokernel.π i)))
  letI : Injective S.X₂ := inferInstanceAs (Injective (Injective.under G))
  let e₀ := genericImageHTwoEquivHOneDirectImageQuotient A F i
  let e₂ := SheafCohomologyDimensionShift.hOneQuotientEquivHTwo S hS
  let Z := AddCommGrpCat.of (ULift.{0} ℤ)
  let Z₀ := (constantSheaf (X A).smallEtaleTopology AddCommGrpCat.{0}).obj Z
  let c := SmallEtaleInverseImageConstants.inverseImageConstantObjectIso
    (j A F) AddCommGrpCat.{0} adj Z
  let a := ExtOneAdjunction.map adj Z₀ Q
  let e₁ := (((extFunctor (C := C₁) 1).mapIso c.symm.op).app Q).addCommGroupIsoToAddEquiv
  have ha : Function.Injective a := ExtOneAdjunction.map_injective adj Z₀ Q
  let b : Sheaf.H (genericUnitImage A F) 2 →+ Sheaf.H G 2 :=
    e₂.toAddMonoidHom.comp (e₁.toAddMonoidHom.comp (a.comp e₀.toAddMonoidHom))
  exact ⟨b, e₂.injective.comp (e₁.injective.comp (ha.comp e₀.injective))⟩

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GenericEtaleUnitSections.genericImageHTwoEmbedding
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
