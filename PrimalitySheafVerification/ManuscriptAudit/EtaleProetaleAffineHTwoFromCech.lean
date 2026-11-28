import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleCohomologyMap
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCechHTwo

/-! Canonical degree-two comparison follows from affine Čech
acyclicity of the actual inverse images of étale injectives. -/

namespace ManuscriptAudit.EtaleProetaleAffineHTwoFromCech

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleProetaleInverseImage (inverseImage)
open EtaleProetaleCohomologyMap (pullback pullback_boundary)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{1}
private abbrev C := Sheaf X.smallEtaleTopology A
private abbrev D := Sheaf (Scheme.ProEt.topology X) A

private theorem etaleGrothendieck : IsGrothendieckAbelian.{1} (C X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology A

attribute [local instance] etaleGrothendieck

local instance : HasExt.{1} (C X) := IsGrothendieckAbelian.hasExt (C X)

local instance : EnoughInjectives (C X) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C X)

local instance : EnoughInjectives (D X) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := D X)

local instance : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

private abbrev Z := (constantSheaf (Scheme.ProEt.topology X) A).obj
  (AddCommGrpCat.of (ULift.{1} ℤ))

set_option maxHeartbeats 3400000 in
/-- Acyclicity on inverse images of étale injectives raises surjectivity
of the actual change-of-sites map by one degree. -/
theorem pullback_succ_surjective (n : ℕ)
    (hPrevious : ∀ F : C X, Function.Surjective (pullback X F n))
    (hInj : ∀ I : C X, Injective I → Subsingleton (Sheaf.H ((inverseImage X).obj I) (n+1)))
    (F : C X) : Function.Surjective (pullback X F (n+1)) := by
  intro x
  let m := Injective.ι F
  let S := ShortComplex.cokernelSequence m
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact m)
      (inferInstanceAs (Mono m)) (inferInstanceAs (Epi (cokernel.π m)))
  let L := inverseImage X
  let hp := hS.map_of_exact L
  letI : Subsingleton (Sheaf.H (L.obj S.X₂) (n + 1)) :=
    hInj S.X₂ (inferInstanceAs (Injective (Injective.under F)))
  have hz : x.comp (Ext.mk₀ (L.map S.f)) (add_zero (n + 1)) = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ (Z X) hp x hz
    (show n + 1 = n + 1 by rfl)
  obtain ⟨b, hb⟩ := hPrevious S.X₃ a
  refine ⟨b.comp hS.extClass rfl, ?_⟩
  exact (pullback_boundary X hS n b).trans (by simpa only [hb] using ha)

variable [IsAffine X]

private theorem HOne_subsingleton_of_affineCech (F : D X)
    (hF : ProetaleAffineCechHTwo.AffineExactAt X F 1) : Subsingleton (Sheaf.H F 1) := by
  let T := Scheme.ProEt.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  letI : IsAffine T.left := inferInstanceAs (IsAffine X)
  let m := Injective.ι F
  exact SheafH1Descent.H1_subsingleton_of_global_lifts m hT
    (ProetaleAffineCechHTwo.cokernel_sections_surjective m hF T)

set_option maxHeartbeats 2800000 in
/-- The actual affine inverse-image Čech comparison in degrees one
and two suffices to make the literal degree-two pullback surjective. -/
theorem pullback_HTwo_surjective
    (hZero : ∀ F : C X, Function.Surjective (pullback X F 0))
    (hOne : ∀ I : C X, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt X ((inverseImage X).obj I) 1)
    (hTwo : ∀ I : C X, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt X ((inverseImage X).obj I) 2)
    (F : C X) : Function.Surjective (pullback X F 2) :=
  pullback_succ_surjective X 1
    (pullback_succ_surjective X 0 hZero (fun I hI ↦
      HOne_subsingleton_of_affineCech X _ (hOne I hI)))
    (fun I hI ↦ ProetaleAffineCechHTwo.HTwo_subsingleton _ (hOne I hI) (hTwo I hI)) F

end
end ManuscriptAudit.EtaleProetaleAffineHTwoFromCech

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleAffineHTwoFromCech.pullback_succ_surjective,
      ``ManuscriptAudit.EtaleProetaleAffineHTwoFromCech.pullback_HTwo_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
