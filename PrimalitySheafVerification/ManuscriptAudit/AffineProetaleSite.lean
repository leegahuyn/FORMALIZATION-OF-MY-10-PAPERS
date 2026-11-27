import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBaseChange

/-! Actual affine weakly étale objects form a dense subsite of the
native small pro-étale site. -/

namespace ManuscriptAudit.AffineProetaleSite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

/-- Affine objects of the actual weakly étale category. -/
def affineObjects : ObjectProperty X.ProEt := fun U ↦ IsAffine U.left

abbrev Affine := (affineObjects X).FullSubcategory

abbrev inclusion : Affine X ⥤ X.ProEt := (affineObjects X).ι

/-- Every actual weakly étale scheme is covered by its ordinary affine opens. -/
instance inclusion_coverDense : (inclusion X).IsCoverDense (Scheme.ProEt.topology X) where
  is_cover U := by
    let C := U.left.affineOpenCover
    let O := C.openCover
    apply (Scheme.ProEt.topology X).superset_covering _ (ProetaleOpenCover.covering U O)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    let W : Affine X := ⟨ProetaleOpenCover.coverObject U O i,
      inferInstanceAs (IsAffine (Spec (C.X i)))⟩
    exact Presieve.in_coverByImage W (ProetaleOpenCover.coverArrow U O i)

abbrev topology : GrothendieckTopology (Affine X) :=
  (inclusion X).inducedTopology (Scheme.ProEt.topology X)

instance inclusion_dense : (inclusion X).IsDenseSubsite (topology X) (Scheme.ProEt.topology X) :=
  inferInstance

/-- The canonical restriction to the actual affine site is an equivalence of abelian sheaves. -/
def sheafEquivalence :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ≌ Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  ((inclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (topology X)
    (Scheme.ProEt.topology X)).asEquivalence

/-- The actual affine chart of a weakly étale object presented by a spectrum. -/
abbrev mk {R : CommRingCat.{u}} (f : Spec R ⟶ X) [WeaklyEtale f] : Affine X :=
  ⟨Scheme.ProEt.mk f, inferInstanceAs (IsAffine (Spec R))⟩

/-- Every affine object is isomorphic to the chart of its global sections. -/
def specIso (U : Affine X) :
    haveI : IsAffine U.obj.left := U.property
    haveI : WeaklyEtale (U.obj.left.isoSpec.inv ≫ U.obj.hom) :=
      haveI : WeaklyEtale U.obj.hom := U.obj.prop
      inferInstance
    U ≅ mk X (U.obj.left.isoSpec.inv ≫ U.obj.hom) := by
  letI : IsAffine U.obj.left := U.property
  letI : WeaklyEtale U.obj.hom := U.obj.prop
  exact ((affineObjects X).fullyFaithfulι.preimageIso
    (MorphismProperty.Over.isoMk U.obj.left.isoSpec (by simp)))

variable {X}
variable {Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)

/-- Actual base change stays in the affine pro-étale subsite of affine schemes. -/
def baseChange : Affine Y ⥤ Affine X :=
  (affineObjects X).lift (inclusion Y ⋙ ProetaleBaseChange.baseChange f) (fun U ↦ by
    change IsAffine (pullback U.obj.hom f)
    exact @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      U.obj.left X Y U.obj.hom f U.property inferInstance inferInstance)

theorem baseChange_comp_inclusion :
    baseChange f ⋙ inclusion X = inclusion Y ⋙ ProetaleBaseChange.baseChange f := rfl

end
end ManuscriptAudit.AffineProetaleSite

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineProetaleSite.inclusion_coverDense,
      ``ManuscriptAudit.AffineProetaleSite.sheafEquivalence,
      ``ManuscriptAudit.AffineProetaleSite.specIso,
      ``ManuscriptAudit.AffineProetaleSite.baseChange_comp_inclusion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
