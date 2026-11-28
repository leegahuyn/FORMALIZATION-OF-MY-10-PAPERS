import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawSections

/-! On an actual affine étale chart the identity stage is terminal.
Consequently the raw colimit comparison detects the actual unit there. -/

namespace ManuscriptAudit.NativeAffineEtaleTerminalStage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleStageCategory (Stage hom)
open EtaleProetaleSiteInclusion (inclusion)
open ProetaleAffineTensor (structureMap specMap)
open NativeAffineEtaleStageSections (etaleObject chartArrow sectionCocone)
open NativeAffineEtaleRawSections (rawSectionCocone isColimit_rawSectionCocone raw_toNative_fac)
open NativeAffineEtaleKanComparison (toNative)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

/-- The given affine étale chart itself, with its identity ring map. -/
abbrev selfStage : Stage A B := Stage.of A B (AlgHom.id A B)

/-- The actual last stage is the affine étale chart itself. -/
def isTerminal_selfStage : IsTerminal (selfStage (A := A) (B := B)) :=
  IsTerminal.ofUniqueHom (fun T ↦ ⟨T.toChart, rfl⟩) (fun _ m ↦ by
    apply Subtype.ext
    ext x
    exact DFunLike.congr_fun m.property x)

variable [WeaklyEtale (structureMap A B)]

private def chartIso :
    ProetaleAffineTensor.object A B ≅ (inclusion (X (A := A))).obj
      (etaleObject (selfStage (A := A) (B := B))) := by
  let s := chartArrow (selfStage (A := A) (B := B))
  have hs : s.left = 𝟙 (ProetaleAffineTensor.spectrum B) := Spec.map_id _
  let t : (inclusion (X (A := A))).obj (etaleObject (selfStage (A := A) (B := B))) ⟶
      ProetaleAffineTensor.object A B :=
    MorphismProperty.Over.homMk (𝟙 _) (Category.id_comp _)
  refine ⟨s, t, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    change s.left ≫ 𝟙 _ = 𝟙 _
    exact (Category.comp_id _).trans hs
  · apply MorphismProperty.Over.Hom.ext
    change 𝟙 _ ≫ s.left = 𝟙 _
    exact (Category.id_comp _).trans hs

set_option maxHeartbeats 3400000 in
/-- At an actual affine étale object, surjectivity of the raw-to-native
map gives surjectivity of the genuine inverse-image unit on sections. -/
theorem unit_app_surjective (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})
    (hRaw : Function.Surjective ((toNative (X (A := A)) I).app
      (op (ProetaleAffineTensor.object A B)))) :
    Function.Surjective (((EtaleProetaleInverseImage.adjunction (X (A := A))).unit.app I).hom.app
      (op (etaleObject (selfStage (A := A) (B := B))))) := by
  let T := selfStage (A := A) (B := B)
  let F := ((EtaleProetaleInverseImage.inverseImage (X (A := A))).obj I).obj
  let η := ((EtaleProetaleInverseImage.adjunction (X (A := A))).unit.app I).hom
  let w := chartIso (A := A) (B := B)
  let c := rawSectionCocone (B := B) I
  let d := (toNative (X (A := A)) I).app (op (ProetaleAffineTensor.object A B))
  letI : IsIso (c.ι.app T) :=
    (isColimit_rawSectionCocone (B := B) I).isIso_ι_app_of_isTerminal T (isTerminal_selfStage)
  have hc : Function.Surjective (c.ι.app T) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  have hi : Function.Injective (F.map w.hom.op) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro x
  obtain ⟨y, hy⟩ := (hRaw.comp hc) (F.map w.hom.op x)
  have h := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (raw_toNative_fac (B := B) I T)) y
  change d (c.ι.app T y) = F.map w.hom.op (η.app (op (etaleObject T)) y) at h
  exact ⟨y, hi (h.symm.trans hy)⟩

end
end ManuscriptAudit.NativeAffineEtaleTerminalStage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineEtaleTerminalStage.isTerminal_selfStage,
      ``ManuscriptAudit.NativeAffineEtaleTerminalStage.unit_app_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
