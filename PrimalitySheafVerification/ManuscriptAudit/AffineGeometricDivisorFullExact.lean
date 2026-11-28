import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorHomEpi
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorHomKernel

/-!
# The divisor exact sequence on the full small étale site

The affine-line divisor sequence uses the actual regular unit sheaf,
its generic-point direct image, and the finite-support rational
skyscraper sheaf. The affine-to-full equivalence preserves its kernel.
-/

namespace ManuscriptAudit.AffineGeometricDivisorFullExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineGeometricDivisorSheaf AffineGeometricDivisorHom
open AffineGeometricDivisorSections AffineGeometricDivisorNaturality
open AffineGeometricDivisorHomKernel AffineGeometricDivisorHomEpi
open GenericEtaleUnitSections

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}

set_option maxHeartbeats 1200000 in
/-- The actual composite from regular units to the divisor sheaf vanishes. -/
theorem regularUnits_comp_divisor :
    genericPointUnitsHom A F ≫ divisorHom K A F = 0 := by
  let m := genericPointUnitsHom A F
  let D := genericUnitImage A F
  have h : m ≫ ((E A).counitIso.app D).inv =
      ((E A).counitIso.app _).inv ≫ (E A).functor.map (affineRegularUnitsHom A F) :=
    (E A).counitIso.inv.naturality m
  change m ≫ (((E A).counitIso.app D).inv ≫ (E A).functor.map (affineDivisorHom K A F)) = 0
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    affineRegularUnits_comp_divisor, Functor.map_zero, comp_zero]

/-- The native geometric affine divisor sequence on the full étale site. -/
def divisorSequence : ShortComplex (Sheaf (X A).smallEtaleTopology AddCommGrpCat.{0}) :=
  ShortComplex.mk (genericPointUnitsHom A F) (divisorHom K A F)
    (regularUnits_comp_divisor K A F)

set_option maxHeartbeats 1800000 in
/-- The full étale divisor sequence is the image of the affine sequence
under the native affine-to-full equivalence. -/
def divisorSequenceIso :
    (affineDivisorSequence K A F).map (E A).functor ≅ divisorSequence K A F := by
  let m := genericPointUnitsHom A F
  let P := KummerUnitsSheaf.fullCoordinateUnitSheaf (X A)
  let D := genericUnitImage A F
  refine ShortComplex.isoMk ((E A).counitIso.app P) ((E A).counitIso.app D)
    (Iso.refl (divisorSheaf K A)) ?_ ?_
  · exact ((E A).counitIso.hom.naturality m).symm
  · change ((E A).counitIso.app D).hom ≫ ((E A).counitIso.app D).inv ≫
        (E A).functor.map (affineDivisorHom K A F) =
      (E A).functor.map (affineDivisorHom K A F) ≫ 𝟙 _
    simp only [Iso.hom_inv_id_assoc, Category.comp_id]

set_option maxHeartbeats 2200000 in
/-- The genuine regular-unit, generic-unit and divisor sheaves form a
short exact sequence on the full small étale site. -/
theorem divisorSequence_shortExact : (divisorSequence K A F).ShortExact := by
  let S := affineDivisorSequence K A F
  let H := (E A).functor
  have hMono : Mono (genericPointUnitsHom A F) := genericPointUnitsHom_mono A F
  letI : Mono (genericPointUnitsHom A F) := hMono
  have h₁ : Mono S.f := show Mono (affineRegularUnitsHom A F) from inferInstance
  have h₂ : PreservesLimit (parallelPair S.g 0) H := inferInstance
  have h₃ : (S.map H).Exact :=
    (affineDivisorSequence_exact K A F).map_of_mono_of_preservesKernel H h₁ h₂
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_iso (divisorSequenceIso K A F) h₃)
    hMono (divisorHom_epi K A F)

set_option maxHeartbeats 1600000 in
/-- The actual generic-point unit cokernel is the finite-support divisor sheaf. -/
def genericPointUnitQuotientIsoDivisor :
    genericPointUnitQuotient A F ≅ divisorSheaf K A :=
  (cokernelIsCokernel (genericPointUnitsHom A F)).coconePointUniqueUpToIso
    (divisorSequence_shortExact K A F).gIsCokernel

end

end ManuscriptAudit.AffineGeometricDivisorFullExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricDivisorFullExact.regularUnits_comp_divisor,
      ``ManuscriptAudit.AffineGeometricDivisorFullExact.divisorSequence_shortExact,
      ``ManuscriptAudit.AffineGeometricDivisorFullExact.genericPointUnitQuotientIsoDivisor] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
