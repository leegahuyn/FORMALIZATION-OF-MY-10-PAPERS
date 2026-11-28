import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleInverseImage

/-! The raw left Kan extension along the actual affine étale
inclusion sheafifies to the actual inverse image. -/

namespace ManuscriptAudit.NativeAffineEtaleKanComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleProetaleSiteInclusion (inclusion)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (X : Scheme.{u})

private abbrev G := AddCommGrpCat.{u + 1}
private abbrev J := Scheme.ProEt.topology X

/-- Actual inclusion in the native pro-étale category. -/
abbrev L := (Scheme.AffineEtale.Spec X ⋙ inclusion X).op

/-- Restrict from the actual small étale site to its affine basis. -/
abbrev affineRestriction :=
  (Scheme.AffineEtale.Spec X).sheafPushforwardContinuous G.{u}
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology

private instance (F : X.AffineEtaleᵒᵖ ⥤ G.{u}) :
    (L X).HasPointwiseLeftKanExtension F :=
  fun _ ↦ inferInstance

variable (I : Sheaf X.smallEtaleTopology G.{u})

/-- The actual raw left Kan extension from affine étale sections. -/
abbrev raw : X.ProEtᵒᵖ ⥤ G.{u} :=
  (L X).lan.obj ((affineRestriction X).obj I).obj

/-- The actual adjunction unit induces the map from the raw Kan
extension to the native inverse image on the given étale sheaf. -/
def toNative : raw X I ⟶ ((EtaleProetaleInverseImage.inverseImage X).obj I).obj :=
  (((L X).lanAdjunction G.{u}).homEquiv _ _).symm
    (((affineRestriction X).map ((EtaleProetaleInverseImage.adjunction X).unit.app I)).hom)

set_option maxHeartbeats 4300000 in
/-- Precomposition with this comparison is bijective against every
actual pro-étale sheaf, so it is exactly a sheafification map. -/
theorem comparison_mem_W : (J X).W (toNative X I) := by
  intro H hH
  let T : Sheaf (J X) G.{u} := ⟨H, hH⟩
  let a := EtaleProetaleInverseImage.adjunction X
  let b := (L X).lanAdjunction G.{u}
  let E := affineRestriction X
  let hE := Functor.FullyFaithful.ofFullyFaithful E
  let F := (EtaleProetaleInverseImage.inverseImage X).obj I
  let e : (F.obj ⟶ H) ≃ (raw X I ⟶ H) :=
    (Sheaf.homEquiv (X := F) (Y := T)).symm.trans
      ((a.homEquiv I T).trans
        (hE.homEquiv.trans (Sheaf.homEquiv.trans ((b.homEquiv ((E.obj I).obj) H).symm))))
  have hfun : (fun p : F.obj ⟶ H ↦ toNative X I ≫ p) = ⇑e := by
    funext p
    apply (b.homEquiv ((E.obj I).obj) H).injective
    have hu : b.homEquiv ((E.obj I).obj) F.obj (toNative X I) =
        (E.map (a.unit.app I)).hom :=
      Equiv.apply_symm_apply _ _
    rw [Adjunction.homEquiv_naturality_right, hu]
    change (E.map (a.unit.app I)).hom ≫
        (whiskerLeft (L X) p) =
      (E.map (a.homEquiv I T ((Sheaf.homEquiv (X := F) (Y := T)).symm p))).hom
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    rfl
  rw [hfun]
  exact e.bijective

end
end ManuscriptAudit.NativeAffineEtaleKanComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineEtaleKanComparison.comparison_mem_W
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
