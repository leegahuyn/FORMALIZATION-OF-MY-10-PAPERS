import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Detecting a kernel on values of abelian sheaves

An objectwise injective map with the objectwise kernel property is a
categorical kernel. Unique objectwise lifts automatically assemble
to a natural transformation.
-/

namespace ManuscriptAudit.SheafObjectwiseKernel

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F G D : Sheaf J AddCommGrpCat.{w}} (a : F ⟶ G) (b : G ⟶ D)

theorem mono_of_value_injective
    (ha : ∀ U : Cᵒᵖ, Function.Injective (a.hom.app U)) : Mono a := by
  letI : Mono a.hom := (NatTrans.mono_iff_mono_app a.hom).mpr fun U =>
    ConcreteCategory.mono_of_injective _ (ha U)
  exact Sheaf.Hom.mono_of_presheaf_mono a

private def lift {H : Sheaf J AddCommGrpCat.{w}} (k : H ⟶ G) (hk : k ≫ b = 0)
    (ha : ∀ U : Cᵒᵖ, Function.Injective (a.hom.app U))
    (hKer : ∀ (U : Cᵒᵖ) (s : G.obj.obj U), b.hom.app U s = 0 →
      ∃ t : F.obj.obj U, a.hom.app U t = s) : H ⟶ F := by
  have hex (U : Cᵒᵖ) (x : H.obj.obj U) :
      ∃ t : F.obj.obj U, a.hom.app U t = k.hom.app U x := by
    apply hKer
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : H ⟶ D => f.hom) hk) U) x
  let y (U : Cᵒᵖ) (x : H.obj.obj U) := Classical.choose (hex U x)
  have hy (U : Cᵒᵖ) (x : H.obj.obj U) : a.hom.app U (y U x) = k.hom.app U x :=
    Classical.choose_spec (hex U x)
  refine ⟨{ app := fun U => AddCommGrpCat.ofHom {
      toFun := y U
      map_zero' := by
        apply ha U
        exact (hy U 0).trans ((k.hom.app U).hom.map_zero.trans (a.hom.app U).hom.map_zero.symm)
      map_add' := fun x z => by
        apply ha U
        rw [hy]
        change (k.hom.app U).hom (x + z) = (a.hom.app U).hom (y U x + y U z)
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) (hy U x).symm (hy U z).symm }
    naturality := fun {U V} f => by
      apply ConcreteCategory.hom_ext
      intro x
      apply ha V
      change a.hom.app V (y V (H.obj.map f x)) = a.hom.app V (F.obj.map f (y U x))
      calc
        _ = k.hom.app V (H.obj.map f x) := hy _ _
        _ = G.obj.map f (k.hom.app U x) :=
          ConcreteCategory.congr_hom (k.hom.naturality f) x
        _ = G.obj.map f (a.hom.app U (y U x)) := congrArg (G.obj.map f) (hy U x).symm
        _ = _ := (ConcreteCategory.congr_hom (a.hom.naturality f) (y U x)).symm }⟩
  
private theorem lift_fac {H : Sheaf J AddCommGrpCat.{w}} (k : H ⟶ G) (hk : k ≫ b = 0)
    (ha : ∀ U : Cᵒᵖ, Function.Injective (a.hom.app U))
    (hKer : ∀ (U : Cᵒᵖ) (s : G.obj.obj U), b.hom.app U s = 0 →
      ∃ t : F.obj.obj U, a.hom.app U t = s) :
    lift a b k hk ha hKer ≫ a = k := by
  apply Sheaf.hom_ext
  ext U : 1
  apply ConcreteCategory.hom_ext
  intro x
  exact Classical.choose_spec _

theorem isLimit_of_value_kernel
    (ha : ∀ U : Cᵒᵖ, Function.Injective (a.hom.app U))
    (h : ∀ (U : Cᵒᵖ) (s : G.obj.obj U),
      b.hom.app U s = 0 ↔ ∃ t : F.obj.obj U, a.hom.app U t = s)
    (w : a ≫ b = 0) : IsLimit (KernelFork.ofι a w) := by
  letI : Mono a := mono_of_value_injective a ha
  refine KernelFork.IsLimit.ofι' a w fun k hk => ?_
  let hKer := fun U s => (h U s).mp
  exact ⟨lift a b k hk ha hKer, lift_fac a b k hk ha hKer⟩

theorem zero_of_value_kernel
    (h : ∀ (U : Cᵒᵖ) (s : G.obj.obj U),
      b.hom.app U s = 0 ↔ ∃ t : F.obj.obj U, a.hom.app U t = s) : a ≫ b = 0 := by
  apply Sheaf.hom_ext
  ext U : 1
  apply ConcreteCategory.hom_ext
  intro t
  exact (h U (a.hom.app U t)).mpr ⟨t, rfl⟩

end

end ManuscriptAudit.SheafObjectwiseKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.SheafObjectwiseKernel.mono_of_value_injective,
      ``ManuscriptAudit.SheafObjectwiseKernel.zero_of_value_kernel,
      ``ManuscriptAudit.SheafObjectwiseKernel.isLimit_of_value_kernel] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
