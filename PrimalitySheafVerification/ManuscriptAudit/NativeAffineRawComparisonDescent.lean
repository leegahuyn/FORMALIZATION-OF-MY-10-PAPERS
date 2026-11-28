import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Grp.FilteredColimits
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawCoproductTransport
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawSingletonSeparationTransport
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleTerminalStage

/-! The actual raw-to-native affine comparison follows from the
literal singleton gluing and the already constructed finite products. -/

namespace ManuscriptAudit.NativeAffineRawComparisonDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap)
open NativeAffineEtaleKanComparison (raw toNative comparison_mem_W)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open EtaleProetaleInverseImage (adjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type} [CommRing A]

private abbrev X := spectrum A

private abbrev J := Scheme.ProEt.topology (X (A := A))

private abbrev G := AddCommGrpCat.{1}

local instance : PreservesLimits (CategoryTheory.forget G) :=
  AddCommGrpCat.adj.rightAdjoint_preservesLimits

variable (I : Sheaf (X (A := A)).smallEtaleTopology G)

set_option maxHeartbeats 4300000 in
/-- Actual chart sections agree with the raw affine-stage colimit
when singleton covers satisfy the actual section gluing condition. -/
theorem comparison_bijective
    (hApprox : ∀ (B : Type) [CommRing B] [Algebra A B],
      WeaklyEtale (structureMap A B) → FiniteTupleApproximation A B)
    (hGlue : ProetaleRawAffineSingletonComparison.AffineSingletonGluing (raw (X (A := A)) I))
    (V : (X (A := A)).ProEt) [IsAffine V.left] :
    Function.Bijective ((toNative (X (A := A)) I).app (op V)) := by
  let η := toNative (X (A := A)) I
  let j := J (A := A)
  have hW : j.W η := comparison_mem_W _ I
  letI : Presheaf.IsLocallyInjective j η := hW.isLocallyInjective
  letI : Presheaf.IsLocallySurjective j η := hW.isLocallySurjective
  let hP := NativeAffineRawCoproductTransport.affineCoproductSections I
  let hS := NativeAffineRawSingletonSeparationTransport.affineSingletonSeparated I hApprox
  exact ⟨ProetaleRawAffineSingletonComparison.injective_app η hP hS V,
    ProetaleRawAffineSingletonComparison.surjective_app η hP hS hGlue V⟩

set_option maxHeartbeats 4300000 in
/-- Degree zero uses the actual terminal object and the actual adjunction unit. -/
theorem unit_terminal_surjective
    (hApprox : ∀ (B : Type) [CommRing B] [Algebra A B],
      WeaklyEtale (structureMap A B) → FiniteTupleApproximation A B)
    (hGlue : ProetaleRawAffineSingletonComparison.AffineSingletonGluing (raw (X (A := A)) I)) :
    Function.Surjective (((adjunction (X (A := A))).unit.app I).hom.app
      (op (Scheme.Etale.mk (𝟙 (X (A := A)))))) := by
  let X₀ := X (A := A)
  have hS : structureMap A A = 𝟙 X₀ := Spec.map_id _
  letI : WeaklyEtale (structureMap A A) := by rw [hS]; infer_instance
  let U := NativeAffineEtaleStageSections.etaleObject
    (NativeAffineEtaleTerminalStage.selfStage (A := A) (B := A))
  let T := Scheme.Etale.mk (𝟙 X₀)
  let e : U ≅ T := MorphismProperty.Over.isoMk (Iso.refl X₀) (by
    change 𝟙 X₀ ≫ 𝟙 X₀ = structureMap A A
    rw [Category.id_comp, hS])
  let f := ((adjunction X₀).unit.app I).hom
  let H := (EtaleProetaleInverseImage.directImage X₀).obj
    ((EtaleProetaleInverseImage.inverseImage X₀).obj I)
  have hs : Function.Surjective (f.app (op U)) :=
    NativeAffineEtaleTerminalStage.unit_app_surjective I
      (comparison_bijective I hApprox hGlue (ProetaleAffineTensor.object A A)).surjective
  have hi : Function.Injective (H.obj.map e.hom.op) := by
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro x
  obtain ⟨y, hy⟩ := hs (H.obj.map e.hom.op x)
  let z := I.obj.map e.inv.op y
  refine ⟨z, hi ?_⟩
  have hz : I.obj.map e.hom.op z = y := by
    change I.obj.map e.hom.op (I.obj.map e.inv.op y) = y
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e.hom_inv_id]
    simp
  have hn := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (f.naturality e.hom.op)) z
  change (f.app (op U)) (I.obj.map e.hom.op z) =
    H.obj.map e.hom.op (f.app (op T) z) at hn
  rw [hz] at hn
  exact hn.symm.trans hy

end
end ManuscriptAudit.NativeAffineRawComparisonDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineRawComparisonDescent.comparison_bijective,
      ``ManuscriptAudit.NativeAffineRawComparisonDescent.unit_terminal_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
