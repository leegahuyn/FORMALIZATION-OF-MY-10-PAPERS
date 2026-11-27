import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GaloisCoverAction
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections

/-!
# Exact sequences of Galois representations on sheaf sections

Evaluating the native sheaf sequence on a finite Galois field cover
is exact as a sequence of genuine group representations once the map
to the last term is surjective on those sections.
-/

namespace ManuscriptAudit.GaloisCoverAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FieldEtaleGaloisCovers

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (F L : Type) [Field F] [Field L] [Algebra F L]
  [Module.Finite F L] [IsGalois F L]

private abbrev U := galoisObject F L
private abbrev D := Sheaf (Spec (CommRingCat.of F)).smallEtaleTopology AddCommGrpCat.{0}

/-- The native section representation as a functor of the coefficient sheaf. -/
def sectionsFunctor : D F ⥤ Rep ℤ (L ≃ₐ[F] L) where
  obj := sectionsRep F L
  map f := sectionsRepMap F L f
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The actual Galois actions on sections of a sheaf short complex. -/
def sectionSequence (S : ShortComplex (D F)) : ShortComplex (Rep ℤ (L ≃ₐ[F] L)) :=
  ShortComplex.mk (sectionsRepMap F L S.f) (sectionsRepMap F L S.g) (by
    ext x
    exact ConcreteCategory.congr_hom
      (congrArg (fun f : S.X₁ ⟶ S.X₃ ↦ f.hom.app (op (U F L))) S.zero) x)

set_option backward.isDefEq.respectTransparency false in
/-- The sequence of section representations is short exact if the
actual map on sections onto the last sheaf is surjective. -/
theorem sectionSequence_shortExact (S : ShortComplex (D F)) (hS : S.ShortExact)
    (hSurj : Function.Surjective (S.g.hom.app (op (U F L)))) :
    (sectionSequence F L S).ShortExact := by
  let W := sectionSequence F L S
  let E : Rep.{0} ℤ (L ≃ₐ[F] L) ⥤ ModuleCat.{0} ℤ :=
    Rep.RepToAction ℤ (L ≃ₐ[F] L) ⋙ Action.forget (ModuleCat.{0} ℤ) (L ≃ₐ[F] L)
  letI : PreservesFiniteLimits E := by dsimp [E]; infer_instance
  letI : PreservesFiniteColimits E := by dsimp [E]; infer_instance
  letI : E.Additive := E.additive_of_preserves_binary_products
  letI : E.Faithful := by dsimp [E]; infer_instance
  have hExact : W.Exact := by
    apply (W.exact_map_iff_of_faithful E).mp
    refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (W.map E)).mpr ?_
    change Function.Exact (fun x ↦ S.f.hom.app (op (U F L)) x)
      (fun x ↦ S.g.hom.app (op (U F L)) x)
    exact SheafShortExactSections.sections_exact S hS (U F L)
  letI : Mono S.f := hS.mono_f
  have hMono : Mono W.f := (Rep.mono_iff_injective (sectionsRepMap F L S.f)).mpr
    (SheafSectionDifference.section_injective S.f (U F L))
  have hEpi : Epi W.g := (Rep.epi_iff_surjective (sectionsRepMap F L S.g)).mpr hSurj
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

end

end ManuscriptAudit.GaloisCoverAction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GaloisCoverAction.sectionSequence_shortExact
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
