import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import PrimalitySheafVerification.ManuscriptAudit.KummerConstantCoefficients
import PrimalitySheafVerification.ManuscriptAudit.KummerSheafSequence

/-!
# The constant coefficient sheaf is the Kummer kernel

The affine roots presheaf is the categorical kernel of the unit-power
presheaf morphism. Sheafification preserves that kernel, identifying it
with the constant sheaf of coefficient roots.
-/

namespace ManuscriptAudit.KummerKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerConstantCoefficients KummerUnitsPresheaf

universe u

noncomputable section

/-- Include the roots of unity in all units object by object. -/
def inclusion (X : Scheme.{u}) (d : ℕ) : roots X d ⟶ units X where
  app U := AddCommGrpCat.ofHom
    (rootsOfUnity d (coordinateRing U.unop)).subtype.toAdditive
  naturality _ := AddCommGrpCat.ext fun _ => Additive.ext (Units.ext rfl)

private theorem inclusion_zero (X : Scheme.{u}) (d : ℕ) : inclusion X d ≫ power X d = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  apply Additive.ext
  exact (mem_rootsOfUnity d (a.toMul : (coordinateRing U.unop)ˣ)).mp a.toMul.prop

private instance (X : Scheme.{u}) (d : ℕ) : Mono (inclusion X d) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro a b h
  apply Additive.ext
  apply Subtype.ext
  exact congrArg Additive.toMul h

private def lift {X : Scheme.{u}} {d : ℕ} {F : X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (k : F ⟶ units X) (hk : k ≫ power X d = 0) : F ⟶ roots X d where
  app U := AddCommGrpCat.ofHom
    { toFun := fun a => Additive.ofMul
        ⟨(k.app U a).toMul, (mem_rootsOfUnity d (k.app U a).toMul).mpr
          (congrArg Additive.toMul (ConcreteCategory.congr_hom (NatTrans.congr_app hk U) a))⟩
      map_zero' := by
        apply Additive.ext
        apply Subtype.ext
        exact congrArg Additive.toMul (map_zero (k.app U).hom)
      map_add' a b := by
        apply Additive.ext
        apply Subtype.ext
        exact congrArg Additive.toMul (map_add (k.app U).hom a b) }
  naturality f := by
    apply AddCommGrpCat.ext
    intro a
    apply Additive.ext
    apply Subtype.ext
    exact congrArg Additive.toMul (NatTrans.naturality_apply k f a)

/-- The roots presheaf is the kernel of the power map on the units presheaf. -/
def rootsIsKernel (X : Scheme.{u}) (d : ℕ) :
    IsLimit (KernelFork.ofι (inclusion X d) (inclusion_zero X d)) := by
  apply KernelFork.IsLimit.ofι'
  intro F k hk
  refine ⟨lift k hk, ?_⟩
  apply NatTrans.ext
  funext U
  exact AddCommGrpCat.ext fun _ => rfl

/-- After sheafification, the ring-roots presheaf still computes the kernel
of the power map. -/
def sheafifiedRootsIsoKernel (X : Scheme.{u}) (d : ℕ) :
    (presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}).obj
        (roots X d) ≅
      kernel (KummerSheafSequence.sheafPower X d) := by
  let F := presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}
  let e : roots X d ≅ kernel (power X d) :=
    (rootsIsKernel X d).conePointUniqueUpToIso (kernelIsKernel (power X d))
  exact F.mapIso e ≪≫ PreservesKernel.iso F (power X d)

/-- The Kummer power kernel is the constant sheaf associated to the roots
of unity of the algebraically closed coefficient field. -/
def constantPowerKernelIso {K : Type u} [Field K] [IsAlgClosed K]
    (R : CommRingCat.{u}) [Algebra K R] (d : ℕ) [NeZero d] [NeZero (d : K)] :
    (constantSheaf (Scheme.AffineEtale.topology (Spec R)) AddCommGrpCat.{u}).obj
        (coefficientGroup K d) ≅
      kernel (KummerSheafSequence.sheafPower (Spec R) d) :=
  constantRootSheafIso (K := K) (d := d) R ≪≫ sheafifiedRootsIsoKernel (Spec R) d

end

end ManuscriptAudit.KummerKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerKernel.rootsIsKernel,
      ``ManuscriptAudit.KummerKernel.sheafifiedRootsIsoKernel,
      ``ManuscriptAudit.KummerKernel.constantPowerKernelIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
