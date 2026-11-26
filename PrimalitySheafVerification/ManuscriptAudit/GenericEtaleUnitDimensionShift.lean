import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismInverseImage
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitResolution
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyDimensionShift

/-!
# Actual generic-point dimension shifting

The first unit resolution remains short exact under the generic-point
direct image. The direct image of its injective middle object stays
injective, so H² of the generic-unit image is H¹ of the direct image of
the actual resolution quotient.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
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

private theorem genericDirectImage_isRightAdjoint : (D A F).IsRightAdjoint := by
  obtain ⟨L, ⟨adj⟩, _⟩ := AffineEtaleMorphism.fullDirectImage_hasLeftExactLeftAdjoint
    (CommRingCat.of A) (CommRingCat.of F) (j A F)
  exact adj.isRightAdjoint

private instance : (D A F).Additive := ⟨by intros; rfl⟩

variable {M : Sheaf (Y F).smallEtaleTopology AddCommGrpCat.{0}}
  (i : fullCoordinateUnitSheaf (Y F) ⟶ M)

/-- The native direct image of the unit cokernel sequence. -/
def unitCokernelSequenceDirectImage :
    ShortComplex (Sheaf (X A).smallEtaleTopology AddCommGrpCat.{0}) :=
  (ShortComplex.cokernelSequence i).map (D A F)

set_option maxHeartbeats 2500000 in
/-- The actual first resolution sequence remains short exact after direct image. -/
theorem unitCokernelSequenceDirectImage_shortExact [Mono i] :
    (unitCokernelSequenceDirectImage A F i).ShortExact := by
  let G := D A F
  letI : G.IsRightAdjoint := genericDirectImage_isRightAdjoint A F
  let S := ShortComplex.cokernelSequence i
  letI : Mono S.f := inferInstanceAs (Mono i)
  have hS : S.Exact := ShortComplex.cokernelSequence_exact i
  have h : (S.map G).Exact :=
    hS.map_of_mono_of_preservesKernel G (inferInstanceAs (Mono S.f)) inferInstance
  exact ShortComplex.ShortExact.mk' h (inferInstanceAs (Mono (G.map i)))
    (directImage_units_cokernel_π_epi A F i)

set_option maxHeartbeats 2200000 in
/-- Degree two of the actual generic unit image identifies with degree
one of the direct image of the actual resolution quotient. -/
def genericImageHTwoEquivHOneDirectImageQuotient [Mono i] [Injective M] :
    Sheaf.H (genericUnitImage A F) 2 ≃+
      Sheaf.H ((D A F).obj (cokernel i)) 1 := by
  let G := D A F
  letI : G.PreservesInjectiveObjects :=
    AffineEtaleMorphism.fullDirectImage_preservesInjectiveObjects
      (CommRingCat.of A) (CommRingCat.of F) (j A F)
  let S := unitCokernelSequenceDirectImage A F i
  letI : Injective S.X₂ := inferInstanceAs (Injective (G.obj M))
  exact (SheafCohomologyDimensionShift.hOneQuotientEquivHTwo S
    (unitCokernelSequenceDirectImage_shortExact A F i)).symm

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GenericEtaleUnitSections.unitCokernelSequenceDirectImage_shortExact,
      ``ManuscriptAudit.GenericEtaleUnitSections.genericImageHTwoEquivHOneDirectImageQuotient] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
