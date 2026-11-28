import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import PrimalitySheafVerification.ManuscriptAudit.InjectiveTerminalCech
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCechTerms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyPositiveShift
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections

/-! Native affine Čech exactness in the first two degrees can be
converted into genuine ordinary H² by two cokernel lifts. -/

namespace ManuscriptAudit.ProetaleAffineCechHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SingletonCoverRefinement (Covers)
open CechNerveLowDegrees (N)
open NativeCechNerve (Cech cochains)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev C := Sheaf (J X) A

local instance : EnoughInjectives (C X) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C X)

/-- The condition uses every actual affine singleton covering in the native site. -/
def AffineExactAt (F : C X) (n : ℕ) : Prop :=
  ∀ {U T : X.ProEt} (f : U ⟶ T), IsAffine U.left → IsAffine T.left →
    Covers (J X) f → (Cech f F.obj).ExactAt n

variable {X}
variable {F I : C X} (m : F ⟶ I) [Mono m]

/-- Actual sections of the cokernel lift on each affine object. -/
theorem cokernel_sections_surjective (hF : AffineExactAt X F 1)
    (T : X.ProEt) [IsAffine T.left] :
    Function.Surjective ((cokernel.π m).hom.app (op T)) := by
  let q := cokernel.π m
  letI : Sheaf.IsLocallySurjective q := (Sheaf.isLocallySurjective_iff_epi' A q).mpr inferInstance
  intro x
  obtain ⟨U, f, ha, _, _, hf, y, hy⟩ :=
    ProetaleAffineSingletonLift.exists_singleton_cover_lift (T := T) q x
  exact NativeCechNerve.exists_global_lift f m hf (hF f ha inferInstance hf) x y hy

private theorem presentation_shortExact : (ShortComplex.cokernelSequence m).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact m)
    (inferInstanceAs (Mono m)) (inferInstanceAs (Epi (cokernel.π m)))

set_option maxHeartbeats 2500000 in
/-- The actual quotient of a mono with degree-one and degree-two affine
Čech exactness has degree-one exactness when the middle sheaf does. -/
theorem quotient_exactAt_one (hF₁ : AffineExactAt X F 1)
    (hF₂ : AffineExactAt X F 2)
    {U T : X.ProEt} (f : U ⟶ T) [IsAffine U.left] [IsAffine T.left]
    (hf : Covers (J X) f) (hI₁ : (Cech f I.obj).ExactAt 1) :
    (Cech f (cokernel m).obj).ExactAt 1 := by
  let S := ShortComplex.cokernelSequence m
  let B := sheafToPresheaf (J X) A ⋙ cochains f
  let P := S.map B
  have hP : P.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact P
    intro n
    let W := N f n
    let Q := P.map (HomologicalComplex.eval A (.up ℕ) n)
    letI : IsAffine W.left := ProetaleAffineCechTerms.isAffine_term f n
    have hExact : Q.Exact := (ShortComplex.ab_exact_iff_function_exact Q).mpr
      (SheafShortExactSections.sections_exact S (presentation_shortExact m) W)
    have hMono : Mono Q.f := (AddCommGrpCat.mono_iff_injective _).mpr
      (SheafSectionDifference.section_injective m W)
    have hEpi : Epi Q.g := (AddCommGrpCat.epi_iff_surjective _).mpr
      (cokernel_sections_surjective m hF₁ W)
    exact ShortComplex.ShortExact.mk' hExact hMono hEpi
  change P.X₃.ExactAt 1
  apply (P.X₃.exactAt_iff_isZero_homology 1).mpr
  let e := hP.homology_exact₃ 1 2 (show (ComplexShape.up ℕ).Rel 1 2 by rfl)
  have hI : IsZero (P.X₂.homology 1) := hI₁.isZero_homology
  have hF : IsZero (P.X₁.homology 2) := (hF₂ f inferInstance inferInstance hf).isZero_homology
  exact e.isZero_X₂ (hI.eq_of_src _ _) (hF.eq_of_tgt _ _)

variable [IsAffine X]

/-- The native H² on an affine scheme vanishes once the actual affine
singleton Čech complexes are exact at degrees one and two. -/
theorem HTwo_subsingleton (F : C X)
    (hF₁ : AffineExactAt X F 1) (hF₂ : AffineExactAt X F 2) :
    Subsingleton (Sheaf.H F 2) := by
  let T := Scheme.ProEt.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  letI : IsAffine T.left := inferInstanceAs (IsAffine X)
  let i := Injective.ι F
  let S := ShortComplex.cokernelSequence i
  let hS := presentation_shortExact i
  let Q := cokernel i
  let j := Injective.ι Q
  have hz : Subsingleton (Sheaf.H Q 1) := by
    apply SheafH1Descent.H1_subsingleton_of_global_lifts j hT
    intro x
    let q := cokernel.π j
    letI : Sheaf.IsLocallySurjective q := (Sheaf.isLocallySurjective_iff_epi' A q).mpr inferInstance
    obtain ⟨U, f, ha, _, _, hf, y, hy⟩ :=
      ProetaleAffineSingletonLift.exists_singleton_cover_lift (T := T) q x
    letI : IsAffine U.left := ha
    have hI : (Cech f (Injective.under F).obj).ExactAt 1 :=
      InjectiveTerminalCech.exactAt_one f hT (Injective.under F)
    have hQ : (Cech f Q.obj).ExactAt 1 := quotient_exactAt_one i hF₁ hF₂ f hf hI
    exact NativeCechNerve.exists_global_lift f j hf hQ x y hy
  letI : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
  exact SheafCohomologyDimensionShift.H_succ_subsingleton_of_injectiveMiddle S hS 1 hz

end
end ManuscriptAudit.ProetaleAffineCechHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineCechHTwo.cokernel_sections_surjective,
      ``ManuscriptAudit.ProetaleAffineCechHTwo.quotient_exactAt_one,
      ``ManuscriptAudit.ProetaleAffineCechHTwo.HTwo_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
