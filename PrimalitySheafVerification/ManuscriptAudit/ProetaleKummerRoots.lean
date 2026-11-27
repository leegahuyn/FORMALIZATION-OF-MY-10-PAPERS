import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import PrimalitySheafVerification.ManuscriptAudit.KummerRootLabels
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerPower

/-! The actual native Kummer kernel consists of roots of unity in
global regular functions, object by object. -/

namespace ManuscriptAudit.ProetaleKummerRoots

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleUnitSheaf ProetaleKummerPower
open KummerRootLabels (mapRoots)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (d : ℕ)

abbrev coordinates (U : X.ProEt) := Scheme.Γ.obj (op U.left)

/-- The covariant coordinate ring roots of unity functor. -/
def ringRoots : CommRingCat.{0} ⥤ AddCommGrpCat.{0} where
  obj R := AddCommGrpCat.of (Additive (rootsOfUnity d R))
  map f := AddCommGrpCat.ofHom (mapRoots d f.hom).toAdditive
  map_id _ := AddCommGrpCat.ext fun _ ↦ Additive.ext (Subtype.ext (Units.ext rfl))
  map_comp _ _ := AddCommGrpCat.ext fun _ ↦ Additive.ext (Subtype.ext (Units.ext rfl))

/-- The native roots-of-unity presheaf in the cohomology universe. -/
def roots : X.ProEtᵒᵖ ⥤ G :=
  (underlying X).op ⋙ Scheme.Γ ⋙ ringRoots d ⋙ AddCommGrpCat.uliftFunctor.{1}

private abbrev space (U : X.ProEtᵒᵖ) := Additive (coordinates X U.unop)ˣ

/-- Regard a root of unity as a unit. -/
def inclusion : roots X d ⟶ (unitSheaf X).obj where
  app U := AddCommGrpCat.uliftFunctor.{1}.map <|
    AddCommGrpCat.ofHom (rootsOfUnity d (coordinates X U.unop)).subtype.toAdditive
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro a
    apply ULift.ext
    apply Additive.ext
    exact Units.ext rfl

private theorem inclusion_zero : inclusion X d ≫ (power X d).hom = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  change (power X d).hom.app U ((inclusion X d).app U a) = 0
  rw [power_eval]
  apply ULift.ext
  apply Additive.ext
  let r : rootsOfUnity d (coordinates X U.unop) := a.down.toMul
  change r.val ^ d = 1
  exact (mem_rootsOfUnity d r.val).mp r.prop

private instance : Mono (inclusion X d) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro a b h
  apply ULift.ext
  apply Additive.ext
  apply Subtype.ext
  exact congrArg (fun z : ULift.{1} (space X U) ↦ z.down.toMul) h

private def lift {F : X.ProEtᵒᵖ ⥤ G} (k : F ⟶ (unitSheaf X).obj)
    (hk : k ≫ (power X d).hom = 0) : F ⟶ roots X d where
  app U := AddCommGrpCat.ofHom
    { toFun := fun a ↦ by
        let u : (coordinates X U.unop)ˣ := (k.app U a).down.toMul
        have he := ConcreteCategory.congr_hom (NatTrans.congr_app hk U) a
        change (power X d).hom.app U (k.app U a) = 0 at he
        rw [power_eval] at he
        have hp := congrArg (fun z : ULift.{1} (space X U) ↦ z.down.toMul) he
        change u ^ d = 1 at hp
        exact ⟨Additive.ofMul ⟨u, (mem_rootsOfUnity d u).mpr hp⟩⟩
      map_zero' := by
        apply ULift.ext
        apply Additive.ext
        apply Subtype.ext
        exact congrArg (fun z : ULift.{1} (space X U) ↦ z.down.toMul) (map_zero (k.app U).hom)
      map_add' a b := by
        apply ULift.ext
        apply Additive.ext
        apply Subtype.ext
        exact congrArg (fun z : ULift.{1} (space X U) ↦ z.down.toMul) (map_add (k.app U).hom a b) }
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro a
    apply ULift.ext
    apply Additive.ext
    apply Subtype.ext
    exact congrArg (fun z : ULift.{1} (space X V) ↦ z.down.toMul)
      (NatTrans.naturality_apply k f a)

private def rootsIsKernel :
    IsLimit (KernelFork.ofι (inclusion X d) (inclusion_zero X d)) := by
  apply KernelFork.IsLimit.ofι'
  intro F k hk
  refine ⟨lift X d k hk, ?_⟩
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  rfl

private def rootsPresheafIso : roots X d ≅ (kernel (power X d)).obj := by
  let P := sheafToPresheaf (J X) G
  let h := (KernelFork.ofι (kernel.ι (power X d)) (kernel.condition (power X d))).mapIsLimit
    (kernelIsKernel (power X d)) P
  exact (rootsIsKernel X d).conePointUniqueUpToIso h

/-- Actual global root sections, as the presheaf kernel of a morphism of sheaves, form a sheaf. -/
theorem roots_isSheaf : Presheaf.IsSheaf (J X) (roots X d) :=
  (Presheaf.isSheaf_of_iso_iff (rootsPresheafIso X d)).mpr (kernel (power X d)).property

/-- The sheaf of actual global roots is the native categorical Kummer kernel. -/
def rootsKernelIso : (⟨roots X d, roots_isSheaf X d⟩ : Sheaf (J X) G) ≅ kernel (power X d) :=
  (sheafToPresheaf (J X) G).preimageIso (rootsPresheafIso X d)

/-- The kernel isomorphism identifies the roots inclusion with the categorical kernel map. -/
@[reassoc]
theorem rootsKernelIso_hom_ι :
    (rootsKernelIso X d).hom.hom ≫ (kernel.ι (power X d)).hom = inclusion X d := by
  let P := sheafToPresheaf (J X) G
  let h := (KernelFork.ofι (kernel.ι (power X d)) (kernel.condition (power X d))).mapIsLimit
    (kernelIsKernel (power X d)) P
  change P.map (rootsKernelIso X d).hom ≫ P.map (kernel.ι (power X d)) = inclusion X d
  rw [rootsKernelIso, Functor.preimageIso_hom]
  change P.map (P.preimage (rootsPresheafIso X d).hom) ≫ P.map (kernel.ι (power X d)) = _
  rw [P.map_preimage]
  have e := (rootsIsKernel X d).conePointUniqueUpToIso_hom_comp h WalkingParallelPair.zero
  change (rootsPresheafIso X d).hom ≫ P.map (kernel.ι (power X d)) = inclusion X d at e
  exact e

end
end ManuscriptAudit.ProetaleKummerRoots

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerRoots.roots_isSheaf,
      ``ManuscriptAudit.ProetaleKummerRoots.rootsKernelIso,
      ``ManuscriptAudit.ProetaleKummerRoots.rootsKernelIso_hom_ι] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
