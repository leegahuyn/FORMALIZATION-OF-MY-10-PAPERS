import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf

/-! The native additive coefficient universe lift on the small étale
site is exact, fully faithful, and commutes with constant sheaves. -/

namespace ManuscriptAudit.EtaleCoefficientUniverseLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev U : A ⥤ B := AddCommGrpCat.uliftFunctor.{1}

variable (X : Scheme.{0})

private abbrev J := X.smallEtaleTopology

/-- Actual universe lift of the coefficients of a small étale sheaf. -/
abbrev lift : Sheaf (J X) A ⥤ Sheaf (J X) B := sheafCompose (J X) U

private theorem locallySurjective_whisker {P Q : X.Etaleᵒᵖ ⥤ A} (t : P ⟶ Q)
    [Presheaf.IsLocallySurjective (J X) t] :
    Presheaf.IsLocallySurjective (J X) (Functor.whiskerRight t U) where
  imageSieve_mem {W} y := by
    let y₀ : Q.obj (op W) := y.down
    apply (J X).superset_covering _ (Presheaf.imageSieve_mem (J X) t y₀)
    intro V f hf
    obtain ⟨x, hx⟩ := hf
    refine ⟨ULift.up x, ?_⟩
    exact congrArg ULift.up hx

private theorem locallyInjective_whisker {P Q : X.Etaleᵒᵖ ⥤ A} (t : P ⟶ Q)
    [Presheaf.IsLocallyInjective (J X) t] :
    Presheaf.IsLocallyInjective (J X) (Functor.whiskerRight t U) where
  equalizerSieve_mem {W} x y h := by
    let x₀ : P.obj W := x.down
    let y₀ : P.obj W := y.down
    have h₀ : t.app W x₀ = t.app W y₀ := congrArg ULift.down h
    apply (J X).superset_covering _ (Presheaf.equalizerSieve_mem (J X) t x₀ y₀ h₀)
    intro V f hf
    exact congrArg ULift.up hf

instance lift_preservesSheafification : (J X).PreservesSheafification U where
  le := by
    intro P Q t ht
    change (J X).W (Functor.whiskerRight t U)
    letI : Presheaf.IsLocallySurjective (J X) t := ht.isLocallySurjective
    letI : Presheaf.IsLocallyInjective (J X) t := ht.isLocallyInjective
    letI := locallySurjective_whisker X t
    letI := locallyInjective_whisker X t
    exact (J X).W_of_isLocallyBijective (Functor.whiskerRight t U)

instance lift_additive : (lift X).Additive where
  map_add {F G} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    change U.map (f.hom.app W + g.hom.app W) = U.map (f.hom.app W) + U.map (g.hom.app W)
    exact U.map_add

instance lift_preservesFiniteLimits : PreservesFiniteLimits (lift X) := by
  let F := sheafToPresheaf (J X) B
  haveI : PreservesFiniteLimits (lift X ⋙ F) := by
    change PreservesFiniteLimits (sheafToPresheaf (J X) A ⋙
      (Functor.whiskeringRight X.Etaleᵒᵖ A B).obj U)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (lift X) F

instance lift_preservesEpimorphisms : (lift X).PreservesEpimorphisms where
  preserves f hf := by
    letI : Presheaf.IsLocallySurjective (J X) f.hom :=
      (Sheaf.isLocallySurjective_iff_epi' A f).mpr hf
    letI : Sheaf.IsLocallySurjective ((lift X).map f) := locallySurjective_whisker X f.hom
    infer_instance

instance lift_preservesFiniteColimits : PreservesFiniteColimits (lift X) := by
  letI : ∀ {F G : Sheaf (J X) A} (f : F ⟶ G), PreservesLimit (parallelPair f 0) (lift X) :=
    fun _ ↦ inferInstance
  letI := Functor.preservesHomology_of_preservesEpis_and_kernels (lift X)
  exact Functor.preservesFiniteColimits_of_preservesHomology (lift X)

/-- The actual constant coefficient sheaves commute with this universe lift. -/
def constantIso :
    constantSheaf (J X) A ⋙ lift X ≅ U ⋙ constantSheaf (J X) B :=
  constantCommuteCompose (J X) U

end
end ManuscriptAudit.EtaleCoefficientUniverseLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleCoefficientUniverseLift.lift_preservesFiniteLimits,
      ``ManuscriptAudit.EtaleCoefficientUniverseLift.lift_preservesFiniteColimits,
      ``ManuscriptAudit.EtaleCoefficientUniverseLift.constantIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
