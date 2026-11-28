import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyHOneCokernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHZero

/-! Degree-two comparison with the native direct image follows from an
actual local lift of the first injective resolution quotient. -/

namespace ManuscriptAudit.ProetaleDirectImageHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleBaseChange (directImage)
open ProetaleInverseImage (adjunction)
open SheafCohomologyDimensionShift (hOneQuotientEquivHTwo)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {Y X : Scheme.{0}} (f : Y ⟶ X) (F : C Y)

local instance (Z : Scheme.{0}) : EnoughInjectives (C Z) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C Z)

private abbrev G := directImage f A
private instance : (G f).IsRightAdjoint := (adjunction f).isRightAdjoint
private instance : (G f).Additive := (G f).additive_of_preserves_binary_products

abbrev kernelInclusion := Injective.ι F
abbrev quotient := cokernel (kernelInclusion F)
abbrev quotientMap := cokernel.π (kernelInclusion F)

private abbrev resolution :=
  ShortComplex.mk (kernelInclusion F) (quotientMap F) (cokernel.condition (kernelInclusion F))

private theorem resolution_shortExact : (resolution F).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (inferInstanceAs (Mono (kernelInclusion F))) (inferInstanceAs (Epi (quotientMap F)))

private theorem image_shortExact (h : Epi ((G f).map (quotientMap F))) :
    ((resolution F).map (G f)).ShortExact := by
  let S := resolution F
  have hx := (resolution_shortExact F).exact.map_of_mono_of_preservesKernel (G f)
    (inferInstanceAs (Mono (kernelInclusion F)))
    (inferInstanceAs (PreservesLimit (parallelPair S.g 0) (G f)))
  exact ShortComplex.ShortExact.mk' hx
    (inferInstanceAs (Mono ((G f).map (kernelInclusion F)))) h

private def sourceShift : Sheaf.H (quotient F) 1 ≃+ Sheaf.H F 2 := by
  letI : Injective (resolution F).X₂ := inferInstanceAs (Injective (Injective.under F))
  exact hOneQuotientEquivHTwo (resolution F) (resolution_shortExact F)

private def imageShift (h : Epi ((G f).map (quotientMap F))) :
    Sheaf.H ((G f).obj (quotient F)) 1 ≃+ Sheaf.H ((G f).obj F) 2 := by
  letI : Injective ((resolution F).map (G f)).X₂ :=
    Injective.injective_of_adjoint (adjunction f) (Injective.under F)
  exact hOneQuotientEquivHTwo ((resolution F).map (G f)) (image_shortExact f F h)

/-- If the first native resolution quotient has local lifts on the target,
the resulting degree-two comparison is the genuine degree-one adjunction
comparison transported through the two connecting isomorphisms. -/
def comparison (h : Epi ((G f).map (quotientMap F))) :
    Sheaf.H ((G f).obj F) 2 →+ Sheaf.H F 2 :=
  (sourceShift F).toAddMonoidHom.comp
    ((ProetaleDirectImageHOne.comparison f (quotient F)).comp (imageShift f F h).symm.toAddMonoidHom)

theorem comparison_injective (h : Epi ((G f).map (quotientMap F))) :
    Function.Injective (comparison f F h) := by
  change Function.Injective ((sourceShift F) ∘ ProetaleDirectImageHOne.comparison f (quotient F) ∘
    (imageShift f F h).symm)
  exact (sourceShift F).injective.comp
    ((ProetaleDirectImageHOne.comparison_injective f (quotient F)).comp (imageShift f F h).symm.injective)

private theorem sections_range (h : Epi ((G f).map (quotientMap F))) :
    ((Sheaf.H.map ((G f).map (quotientMap F)) 0).range).map
      (ProetaleDirectImageHZero.equivalence f (quotient F)).toAddMonoidHom =
        (Sheaf.H.map (quotientMap F) 0).range := by
  let e := ProetaleDirectImageHZero.equivalence f (quotient F)
  let eI := ProetaleDirectImageHZero.equivalence f (Injective.under F)
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨eI a, (ProetaleDirectImageHZero.natural f (quotientMap F) a).symm⟩
  · rintro ⟨a, rfl⟩
    let b := eI.symm a
    refine ⟨Sheaf.H.map ((G f).map (quotientMap F)) 0 b, ⟨b, rfl⟩, ?_⟩
    change e (Sheaf.H.map ((G f).map (quotientMap F)) 0 b) =
      Sheaf.H.map (quotientMap F) 0 a
    rw [ProetaleDirectImageHZero.natural]
    exact congrArg (Sheaf.H.map (quotientMap F) 0) (eI.apply_symm_apply a)

set_option maxHeartbeats 4500000 in
/-- When the first actual injective quotient remains epic under direct
image, the two native degree-one groups are canonically equivalent via
their global-section cokernels. -/
def hOneEquivOfImageEpi (h : Epi ((G f).map (quotientMap F))) :
    Sheaf.H ((G f).obj F) 1 ≃+ Sheaf.H F 1 := by
  letI : Injective ((resolution F).map (G f)).X₂ :=
    Injective.injective_of_adjoint (adjunction f) (Injective.under F)
  let e := ProetaleDirectImageHZero.equivalence f (quotient F)
  let eq := QuotientAddGroup.congr _ _ e (sections_range f F h)
  letI : Injective (resolution F).X₂ := inferInstanceAs (Injective (Injective.under F))
  let source := SheafCohomologyHOneCokernel.hOneEquiv ((resolution F).map (G f))
    (image_shortExact f F h)
  let target := SheafCohomologyHOneCokernel.hOneEquiv (resolution F) (resolution_shortExact F)
  exact source.symm.trans (eq.trans target)

/-- Two native local lifting properties suffice for the actual
degree-two isomorphism with cohomology on the source scheme. -/
def hTwoEquivOfImageEpi
    (h₁ : Epi ((G f).map (quotientMap F)))
    (h₂ : Epi ((G f).map (quotientMap (quotient F)))) :
    Sheaf.H ((G f).obj F) 2 ≃+ Sheaf.H F 2 :=
  (imageShift f F h₁).symm.trans
    ((hOneEquivOfImageEpi f (quotient F) h₂).trans (sourceShift F))

end
end ManuscriptAudit.ProetaleDirectImageHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleDirectImageHTwo.comparison_injective,
      ``ManuscriptAudit.ProetaleDirectImageHTwo.hOneEquivOfImageEpi,
      ``ManuscriptAudit.ProetaleDirectImageHTwo.hTwoEquivOfImageEpi] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
