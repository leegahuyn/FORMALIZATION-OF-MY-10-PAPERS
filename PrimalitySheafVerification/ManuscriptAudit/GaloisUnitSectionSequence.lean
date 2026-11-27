import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import PrimalitySheafVerification.ManuscriptAudit.EtaleFieldUnitLocalLift
import PrimalitySheafVerification.ManuscriptAudit.GaloisCoverAction
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-! The true unit quotient sequence gives a short exact Galois representation sequence. -/

namespace ManuscriptAudit.GaloisCoverAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FieldEtaleGaloisCovers KummerUnitsSheaf

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [IsGalois K L]

private abbrev X := Spec (CommRingCat.of K)
private abbrev U := galoisObject K L
private abbrev fieldUnitSheaf := fullCoordinateUnitSheaf (X K)

def unitSectionIso :
    sectionsRep K L (fieldUnitSheaf K) ≅ Rep.ofAlgebraAutOnUnits K L := by
  let e : ((fieldUnitSheaf K).obj.obj (op (U K L))) ≃+ Additive Lˣ :=
    (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of L))).addCommGroupIsoToAddEquiv
  apply Rep.mkIso
  refine Representation.Equiv.mk e.toIntLinearEquiv ?_
  intro σ
  apply LinearMap.ext
  intro x
  change e ((fieldUnitSheaf K).obj.map (automorphism K L σ).op x) =
    Additive.ofMul (Units.map σ.toRingHom.toMonoidHom (Additive.toMul (e x)))
  have h := ringUnits.congr_map
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ.toRingHom))
  exact ConcreteCategory.congr_hom h x

variable {I : Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}} (i : fieldUnitSheaf K ⟶ I)

def unitSectionSequence : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (sectionsRepMap K L i) (sectionsRepMap K L (cokernel.π i)) (by
    ext x
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : fieldUnitSheaf K ⟶ cokernel i => f.hom.app (op (U K L)))
        (cokernel.condition i)) x
    exact h)

set_option backward.isDefEq.respectTransparency false in
theorem unitSectionSequence_shortExact [Mono i] :
    (unitSectionSequence K L i).ShortExact := by
  let S := unitSectionSequence K L i
  let E : Rep.{0} ℤ (L ≃ₐ[K] L) ⥤ ModuleCat.{0} ℤ :=
    Rep.RepToAction ℤ (L ≃ₐ[K] L) ⋙ Action.forget (ModuleCat.{0} ℤ) (L ≃ₐ[K] L)
  letI : PreservesFiniteLimits E := by dsimp [E]; infer_instance
  letI : PreservesFiniteColimits E := by dsimp [E]; infer_instance
  letI : E.Additive := E.additive_of_preserves_binary_products
  letI : E.Faithful := by dsimp [E]; infer_instance
  have hExact : S.Exact := by
    apply (S.exact_map_iff_of_faithful E).mp
    refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map E)).mpr ?_
    change Function.Exact (fun x => i.hom.app (op (U K L)) x)
      (fun x => (cokernel.π i).hom.app (op (U K L)) x)
    exact SheafSectionDifference.cokernel_sections_exact i (U K L)
  have hMono : Mono S.f := (Rep.mono_iff_injective (sectionsRepMap K L i)).mpr
    (SheafSectionDifference.section_injective i (U K L))
  have hEpi : Epi S.g := (Rep.epi_iff_surjective (sectionsRepMap K L (cokernel.π i))).mpr
    (EtaleObjectRestriction.unitsCokernel_sections_surjective_of_field i (U K L) L (Iso.refl _))
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

end
end ManuscriptAudit.GaloisCoverAction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GaloisCoverAction.unitSectionIso,
      ``ManuscriptAudit.GaloisCoverAction.unitSectionSequence_shortExact] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
