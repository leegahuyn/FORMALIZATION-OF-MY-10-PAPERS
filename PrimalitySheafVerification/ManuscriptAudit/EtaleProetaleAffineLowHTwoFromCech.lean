import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleCoefficientCohomologyMap
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleHZeroUnitSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCechHTwo

/-! The native comparison in degree two can start directly
with small étale coefficients. Its dimension-shifting resolution
uses small étale injectives. -/

namespace ManuscriptAudit.EtaleProetaleAffineLowHTwoFromCech

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleCoefficientUniverseLift (lift)
open EtaleProetaleInverseImage (inverseImage adjunction)
open EtaleProetaleCohomologyMap (pullback pullback_boundary)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev C := Sheaf X.smallEtaleTopology A
private abbrev C' := Sheaf X.smallEtaleTopology B
private abbrev D := Sheaf (Scheme.ProEt.topology X) B

private theorem lowGrothendieck : IsGrothendieckAbelian.{0} (C X) :=
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X A

private theorem liftedGrothendieck : IsGrothendieckAbelian.{1} (C' X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology B

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] lowGrothendieck liftedGrothendieck

local instance : HasExt.{1} (C' X) := IsGrothendieckAbelian.hasExt (C' X)
local instance : EnoughInjectives (C X) :=
  IsGrothendieckAbelian.enoughInjectives.{0} (C := C X)
local instance : EnoughInjectives (D X) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := D X)
local instance : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

/-- The actual coefficient lift followed by the actual native inverse image. -/
abbrev liftedImage : C X ⥤ D X := lift X ⋙ inverseImage X

private abbrev Z := (constantSheaf (Scheme.ProEt.topology X) B).obj
  (AddCommGrpCat.of (ULift.{1} ℤ))

/-- The literal comparison from small étale cohomology, with genuine
native pro-étale coefficients as the target. -/
def comparison (F : C X) (n : ℕ) : Sheaf.H F n →+ Sheaf.H ((liftedImage X).obj F) n :=
  (pullback X ((lift X).obj F) n).comp (EtaleCoefficientCohomologyMap.comparison X F n)

private theorem comparison_boundary {S : ShortComplex (C X)} (hS : S.ShortExact)
    (n : ℕ) (x : Sheaf.H S.X₃ n) :
    comparison X S.X₁ (n+1) (x.comp hS.extClass rfl) =
      (comparison X S.X₃ n x).comp
        (((hS.map_of_exact (lift X)).map_of_exact (inverseImage X)).extClass) rfl := by
  simp only [comparison, AddMonoidHom.comp_apply, EtaleCoefficientCohomologyMap.comparison_boundary,
    pullback_boundary]

set_option maxHeartbeats 4000000 in
private theorem comparison_succ_surjective (n : ℕ)
    (hPrevious : ∀ F : C X, Function.Surjective (comparison X F n))
    (hInj : ∀ I : C X, Injective I →
      Subsingleton (Sheaf.H ((liftedImage X).obj I) (n+1)))
    (F : C X) : Function.Surjective (comparison X F (n+1)) := by
  intro x
  let m := Injective.ι F
  let S := ShortComplex.cokernelSequence m
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact m)
      (inferInstanceAs (Mono m)) (inferInstanceAs (Epi (cokernel.π m)))
  let hp := (hS.map_of_exact (lift X)).map_of_exact (inverseImage X)
  letI : Subsingleton (Sheaf.H ((liftedImage X).obj S.X₂) (n + 1)) :=
    hInj S.X₂ (inferInstanceAs (Injective (Injective.under F)))
  have hz : x.comp (Ext.mk₀ ((liftedImage X).map S.f)) (add_zero (n + 1)) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ (Z X) hp x hz
    (show n + 1 = n + 1 by rfl)
  obtain ⟨b, hb⟩ := hPrevious S.X₃ a
  refine ⟨b.comp hS.extClass rfl, ?_⟩
  exact (comparison_boundary X hS n b).trans (by simpa only [hb] using ha)

variable [IsAffine X]

private theorem HOne_subsingleton_of_affineCech (F : D X)
    (hF : ProetaleAffineCechHTwo.AffineExactAt X F 1) : Subsingleton (Sheaf.H F 1) := by
  let T := Scheme.ProEt.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  letI : IsAffine T.left := inferInstanceAs (IsAffine X)
  let m := Injective.ι F
  exact SheafH1Descent.H1_subsingleton_of_global_lifts m hT
    (ProetaleAffineCechHTwo.cokernel_sections_surjective m hF T)

set_option maxHeartbeats 4100000 in
/-- Only small étale injectives are needed to obtain surjectivity in
degree two for the actual small-étale to native-pro-étale map. -/
theorem comparison_HTwo_surjective
    (hZero : ∀ F : C X, Function.Surjective (((adjunction X).unit.app ((lift X).obj F)).hom.app
      (op (Scheme.Etale.mk (𝟙 X)))))
    (hOne : ∀ I : C X, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt X ((liftedImage X).obj I) 1)
    (hTwo : ∀ I : C X, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt X ((liftedImage X).obj I) 2)
    (F : C X) : Function.Surjective (comparison X F 2) := by
  have h₀ (E : C X) : Function.Surjective (comparison X E 0) :=
    (EtaleProetaleHZeroUnitSurjectivity.pullback_zero_surjective X ((lift X).obj E) (hZero E)).comp
      (EtaleCoefficientCohomologyMap.comparison_zero_surjective X E)
  exact comparison_succ_surjective X 1
    (comparison_succ_surjective X 0 h₀ (fun I hI ↦
      HOne_subsingleton_of_affineCech X _ (hOne I hI)))
    (fun I hI ↦ ProetaleAffineCechHTwo.HTwo_subsingleton _ (hOne I hI) (hTwo I hI)) F

end
end ManuscriptAudit.EtaleProetaleAffineLowHTwoFromCech

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleProetaleAffineLowHTwoFromCech.comparison_HTwo_surjective
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
