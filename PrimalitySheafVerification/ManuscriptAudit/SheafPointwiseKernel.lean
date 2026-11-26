import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! An injective first arrow with actual pointwise kernel equality is a
kernel in the category of abelian sheaves. -/

namespace ManuscriptAudit.SheafPointwiseKernel

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))

/-- Assemble pointwise injective exactness into the native sheaf kernel. -/
def kernel_isLimit
    (hinj : ∀ U, Function.Injective (S.f.hom.app U))
    (hexact : ∀ U, Function.Exact (S.f.hom.app U) (S.g.hom.app U)) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  classical
  letI : Mono S.f := Sheaf.mono_of_injective S.f hinj
  refine KernelFork.IsLimit.ofι' S.f S.zero (fun {T} k hk => ?_)
  have existsLift (U : Cᵒᵖ) (s : T.obj.obj U) :
      ∃ t : S.X₁.obj.obj U, S.f.hom.app U t = k.hom.app U s := by
    apply (hexact U _).mp
    exact ConcreteCategory.congr_hom (congrArg (fun a => a.hom.app U) hk) s
  let l (U : Cᵒᵖ) (s : T.obj.obj U) : S.X₁.obj.obj U :=
    Classical.choose (existsLift U s)
  have hl (U : Cᵒᵖ) (s : T.obj.obj U) :
      S.f.hom.app U (l U s) = k.hom.app U s :=
    Classical.choose_spec (existsLift U s)
  let lHom : T ⟶ S.X₁ :=
    ⟨{ app U := AddCommGrpCat.ofHom
        { toFun := l U
          map_zero' := by
            apply hinj U
            simp only [hl, map_zero]
          map_add' := by
            intro x y
            apply hinj U
            simp only [hl, map_add] }
       naturality := by
         intro U V f
         apply ConcreteCategory.hom_ext
         intro s
         change l V (T.obj.map f s) = S.X₁.obj.map f (l U s)
         apply hinj V
         rw [hl]
         have h₁ := ConcreteCategory.congr_hom (S.f.hom.naturality f) (l U s)
         have h₂ := ConcreteCategory.congr_hom (k.hom.naturality f) s
         change S.f.hom.app V (S.X₁.obj.map f (l U s)) =
           S.X₂.obj.map f (S.f.hom.app U (l U s)) at h₁
         change k.hom.app V (T.obj.map f s) =
           S.X₂.obj.map f (k.hom.app U s) at h₂
         rw [h₁, hl, h₂] }⟩
  refine ⟨lHom, ?_⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  exact hl U s

end
end ManuscriptAudit.SheafPointwiseKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafPointwiseKernel.kernel_isLimit
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
