import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineModeledEtaleCechPositiveOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRelativeDescent
import Mathlib.Algebra.Homology.QuasiIso

/-! A genuine relative affine étale arrow is modeled at a finite
étale base stage and its native positive cochains are exact. -/

namespace ManuscriptAudit.AffineRelativeEtaleCechPositiveOfApproximation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)
open AffineEtaleCoverModelIso (baseIso coverIso coverIso_leg)
open NativeAffineCechRawComparison (nativeArrow nativePresheaf)
open NativeCechNerve (Cech)
open EtaleCoefficientUniverseLift (lift)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R₀ : Type) [CommRing R₀]

private abbrev A := R₀
private abbrev X := Spec (CommRingCat.of (A R₀))

variable (hApprox : EtaleBaseChangeFiniteApproximation.HasWeaklyEtaleApproximations R₀)

variable (B F : Type) [CommRing B] [CommRing F] [Algebra (A R₀) B] [Algebra B F]
  [WeaklyEtale (structureMap (A R₀) B)] [Algebra.Etale B F]

private abbrev k := CommRingCat.ofHom (algebraMap (A R₀) B)

abbrev givenArrow := (AffineCechRelativeArrowColimit.arrows (k R₀ B)).obj
  (CommRingCat.mkUnder (CommRingCat.of B) F)

instance base_weaklyEtale : WeaklyEtale (Spec.map (givenArrow R₀ B F).left.hom) :=
  inferInstanceAs (WeaklyEtale (structureMap (A R₀) B))

instance cover_weaklyEtale : WeaklyEtale (Spec.map (givenArrow R₀ B F).right.hom) := by
  let f := givenArrow R₀ B F
  letI : Etale (Spec.map f.hom.right) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap B F))).mpr ((RingHom.etale_algebraMap).mpr inferInstance)
  letI : WeaklyEtale (Spec.map f.left.hom) := base_weaklyEtale R₀ B F
  change WeaklyEtale (Spec.map f.right.hom)
  rw [← Under.w f.hom, Spec.map_comp]
  infer_instance

variable (I : Sheaf (X R₀).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]

include hApprox in
set_option maxHeartbeats 7800000 in
/-- Exactness is invariant under the actual isomorphism from the
descended finite model to the original affine relative étale arrow. -/
theorem exactAt_succ (n : ℕ) :
    (Cech (nativeArrow (givenArrow R₀ B F)) (nativePresheaf ((lift (X R₀)).obj I))).ExactAt (n + 1) := by
  obtain ⟨Q, hQR, hQA, hQE, q, E, hER, hEA, hEE, ⟨e⟩⟩ :=
    AffineEtaleStageRelativeDescent.exists_model (D := F)
      (AffineNativeRawSectionsOfApproximation.finite_approximation R₀ hApprox B inferInstance)
  letI : CommRing Q := hQR
  letI : Algebra (A R₀) Q := hQA
  letI : Algebra.Etale (A R₀) Q := hQE
  letI : CommRing E := hER
  letI : Algebra Q E := hEA
  letI : Algebra.Etale Q E := hEE
  letI : Algebra (A R₀) F := Algebra.compHom F (algebraMap (A R₀) B)
  letI : IsScalarTower (A R₀) B F := IsScalarTower.of_algebraMap_eq' rfl
  let T := Stage.of (A R₀) B q
  let f := (AffineModeledEtaleCechPositiveOfApproximation.arrowCocone R₀ T E).pt
  let g := givenArrow R₀ B F
  let i : f ≅ g := Arrow.isoMk (baseIso T) (coverIso T E e) (coverIso_leg T E e).symm
  let j := AffineCechSiteArrowDiagram.siteIsoOfRingIso @WeaklyEtale
    (f := f) (g := g) inferInstance inferInstance inferInstance inferInstance i
  let P := nativePresheaf ((lift (X R₀)).obj I)
  let h := (NativeCechArrowFunctor.cochains P).mapIso j.symm.op
  exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt h.hom (n + 1)).mp
    (AffineModeledEtaleCechPositiveOfApproximation.exactAt_succ R₀ hApprox T E I n)

end
end ManuscriptAudit.AffineRelativeEtaleCechPositiveOfApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineRelativeEtaleCechPositiveOfApproximation.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
