import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismInverseImage
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-!
# Vanishing of degree-one cohomology under direct image

The actual étale direct image along a morphism of affine spectra
preserves injective sheaves and kernels. The resulting cokernel embeds
in the direct image of the original cokernel. Since base change sends
the terminal site object to a terminal object, vanishing of degree-one
cohomology on the source gives the required global lifts.
-/

namespace ManuscriptAudit.AffineEtaleMorphism

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

set_option maxHeartbeats 2500000 in
/-- Vanishing of H¹ is preserved by the actual full small étale direct image
for a morphism of affine spectra. -/
theorem fullDirectImage_HOne_subsingleton (R S : CommRingCat.{u}) (f : Spec S ⟶ Spec R)
    (F : Sheaf (Spec S).smallEtaleTopology AddCommGrpCat.{u})
    (hF : Subsingleton (Sheaf.H F 1)) :
    Subsingleton (Sheaf.H ((SmallEtaleBaseChange.directImage f AddCommGrpCat.{u}).obj F) 1) := by
  let X := Spec S
  let Y := Spec R
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let D := SmallEtaleBaseChange.directImage f AddCommGrpCat.{u}
  letI : IsGrothendieckAbelian.{u} C :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{u} (C := C)
  obtain ⟨L, ⟨a⟩, hL⟩ := fullDirectImage_hasLeftExactLeftAdjoint R S f
  letI : PreservesFiniteLimits L := hL
  letI : D.IsRightAdjoint := a.isRightAdjoint
  letI : D.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms a
  let i : F ⟶ Injective.under F := Injective.ι F
  letI : Mono i := inferInstanceAs (Mono (Injective.ι F))
  let S₀ := ShortComplex.cokernelSequence i
  have h₀ : S₀.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i) (inferInstanceAs (Mono i))
    (inferInstanceAs (Epi (cokernel.π i)))
  let S₁ := S₀.map D
  letI : Mono S₁.f := inferInstanceAs (Mono (D.map i))
  letI : Injective S₁.X₂ := inferInstanceAs (Injective (D.obj (Injective.under F)))
  have h₁ : S₁.Exact := h₀.exact.map_of_mono_of_preservesKernel D h₀.mono_f inferInstance
  let k := cokernel.desc S₁.f S₁.g S₁.zero
  letI : Mono k := S₁.exact_iff_mono_cokernel_desc.mp h₁
  let TY := ⊤_ Y.Etale
  let B := SmallEtaleBaseChange.etaleBaseChange f
  letI : PreservesFiniteLimits B := SmallEtaleBaseChange.preservesFiniteLimits f
  let hY : IsTerminal TY := terminalIsTerminal
  let hX : IsTerminal (B.obj TY) := hY.isTerminalObj B TY
  have hSurj : Function.Surjective (S₁.g.hom.app (op TY)) := by
    change Function.Surjective ((cokernel.π i).hom.app (op (B.obj TY)))
    exact SheafShortExactSections.sections_surjective_of_HOne S₀ h₀ hX hF
  apply SheafH1Descent.H1_subsingleton_of_global_lifts S₁.f hY
  intro x
  obtain ⟨y, hy⟩ := hSurj (k.hom.app (op TY) x)
  refine ⟨y, SheafSectionDifference.section_injective k TY ?_⟩
  have eq := congrArg (fun g : S₁.X₂ ⟶ S₁.X₃ ↦ g.hom.app (op TY))
    (cokernel.π_desc S₁.f S₁.g S₁.zero)
  exact (ConcreteCategory.congr_hom eq y).trans hy

end

end ManuscriptAudit.AffineEtaleMorphism

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

/-- The actual generic-point direct image of regular units has zero H¹. -/
theorem genericUnitImage_HOne_subsingleton (A F : Type) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] :
    Subsingleton (Sheaf.H (genericUnitImage A F) 1) :=
  AffineEtaleMorphism.fullDirectImage_HOne_subsingleton (CommRingCat.of A) (CommRingCat.of F)
    (Spec.map (CommRingCat.ofHom (algebraMap A F)))
    (KummerUnitsSheaf.fullCoordinateUnitSheaf (Spec (CommRingCat.of F)))
    (KummerUnitsSheaf.unitHOne_subsingleton_of_pid F)

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleMorphism.fullDirectImage_HOne_subsingleton,
      ``ManuscriptAudit.GenericEtaleUnitSections.genericUnitImage_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
