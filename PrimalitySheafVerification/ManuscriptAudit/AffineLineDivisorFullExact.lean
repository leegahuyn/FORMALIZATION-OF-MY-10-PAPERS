import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHomEpi
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHomKernel

/-!
# The divisor exact sequence on the full small étale site

The affine-line divisor sequence uses the actual regular unit sheaf,
its generic-point direct image, and the finite-support rational
skyscraper sheaf. The affine-to-full equivalence preserves its kernel.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open GenericEtaleUnitSections

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K F : Type) [Field K] [IsAlgClosed K] [Field F]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]

private abbrev A := Polynomial K
private abbrev E := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}

set_option maxHeartbeats 1200000 in
/-- The actual composite from regular units to the divisor sheaf vanishes. -/
theorem regularUnits_comp_divisor :
    genericPointUnitsHom (A K) F ≫ divisorHom K F = 0 := by
  let m := genericPointUnitsHom (A K) F
  let D := genericUnitImage (A K) F
  have h : m ≫ ((E K).counitIso.app D).inv =
      ((E K).counitIso.app _).inv ≫ (E K).functor.map (affineRegularUnitsHom K F) :=
    (E K).counitIso.inv.naturality m
  change m ≫ (((E K).counitIso.app D).inv ≫ (E K).functor.map (affineDivisorHom K F)) = 0
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    affineRegularUnits_comp_divisor, Functor.map_zero, comp_zero]

/-- The native affine-line divisor sequence on the full étale site. -/
def divisorSequence : ShortComplex (Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}) :=
  ShortComplex.mk (genericPointUnitsHom (A K) F) (divisorHom K F)
    (regularUnits_comp_divisor K F)

set_option maxHeartbeats 1800000 in
/-- The full étale divisor sequence is the image of the affine sequence
under the native affine-to-full equivalence. -/
def divisorSequenceIso :
    (affineDivisorSequence K F).map (E K).functor ≅ divisorSequence K F := by
  let m := genericPointUnitsHom (A K) F
  let P := KummerUnitsSheaf.fullCoordinateUnitSheaf (X K)
  let D := genericUnitImage (A K) F
  refine ShortComplex.isoMk ((E K).counitIso.app P) ((E K).counitIso.app D)
    (Iso.refl (divisorSheaf K)) ?_ ?_
  · exact ((E K).counitIso.hom.naturality m).symm
  · change ((E K).counitIso.app D).hom ≫ ((E K).counitIso.app D).inv ≫
        (E K).functor.map (affineDivisorHom K F) =
      (E K).functor.map (affineDivisorHom K F) ≫ 𝟙 _
    simp only [Iso.hom_inv_id_assoc, Category.comp_id]

set_option maxHeartbeats 2200000 in
/-- The genuine regular-unit, generic-unit and divisor sheaves form a
short exact sequence on the full small étale site. -/
theorem divisorSequence_shortExact : (divisorSequence K F).ShortExact := by
  let S := affineDivisorSequence K F
  let H := (E K).functor
  have hMono : Mono (genericPointUnitsHom (A K) F) := genericPointUnitsHom_mono (A K) F
  letI : Mono (genericPointUnitsHom (A K) F) := hMono
  have h₁ : Mono S.f := show Mono (affineRegularUnitsHom K F) from inferInstance
  have h₂ : PreservesLimit (parallelPair S.g 0) H := inferInstance
  have h₃ : (S.map H).Exact :=
    (affineDivisorSequence_exact K F).map_of_mono_of_preservesKernel H h₁ h₂
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_iso (divisorSequenceIso K F) h₃)
    hMono (divisorHom_epi K F)

set_option maxHeartbeats 1600000 in
/-- The actual generic-point unit cokernel is the finite-support divisor sheaf. -/
def genericPointUnitQuotientIsoDivisor :
    genericPointUnitQuotient (A K) F ≅ divisorSheaf K :=
  (cokernelIsCokernel (genericPointUnitsHom (A K) F)).coconePointUniqueUpToIso
    (divisorSequence_shortExact K F).gIsCokernel

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.regularUnits_comp_divisor,
      ``ManuscriptAudit.AffineLineDivisorSheaf.divisorSequence_shortExact,
      ``ManuscriptAudit.AffineLineDivisorSheaf.genericPointUnitQuotientIsoDivisor] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
