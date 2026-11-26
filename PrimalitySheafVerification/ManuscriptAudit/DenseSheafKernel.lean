import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Kernel recognition on a cover-dense subsite

An additive sheaf morphism exhibits the kernel of a second morphism when
its sections identify the kernel on every object of a cover-dense, locally
full subsite. The sectionwise lifts assemble by uniqueness and extend
to the full site using cover density.
-/

namespace ManuscriptAudit.DenseSheafKernel

open CategoryTheory CategoryTheory.Limits

universe u

variable {C D : Type*} [Category* C] [Category* D]
  (J : GrothendieckTopology D) (I : C ⥤ D)
  [I.IsCoverDense J] [I.IsLocallyFull J]

/-- Equality of additive sheaf maps can be checked on the cover-dense subsite. -/
theorem hom_ext {P Q : Sheaf J AddCommGrpCat.{u}} {a b : P ⟶ Q}
    (h : ∀ U : Cᵒᵖ, a.hom.app (I.op.obj U) = b.hom.app (I.op.obj U)) : a = b := by
  apply Sheaf.hom_ext
  apply (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense (K := J)
    I P.obj Q.obj Q.property).1
  apply NatTrans.ext
  funext U
  exact h U

set_option backward.isDefEq.respectTransparency false in
/-- Sectionwise exactness and injectivity on the dense subsite give a kernel fork. -/
noncomputable def isLimit {P Q R : Sheaf J AddCommGrpCat.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (hab : a ≫ b = 0) [Mono a]
    (ha : ∀ U : Cᵒᵖ, Function.Injective (a.hom.app (I.op.obj U)).hom)
    (he : ∀ U : Cᵒᵖ, Function.Exact (a.hom.app (I.op.obj U)).hom
      (b.hom.app (I.op.obj U)).hom) :
    IsLimit (KernelFork.ofι a hab) := by
  classical
  apply KernelFork.IsLimit.ofι' a hab
  intro W k hk
  have hzero (U : Cᵒᵖ) (x : W.obj.obj (I.op.obj U)) :
      b.hom.app (I.op.obj U) (k.hom.app (I.op.obj U) x) = 0 := by
    have eq := NatTrans.congr_app (congrArg (fun t : W ⟶ R ↦ t.hom) hk) (I.op.obj U)
    exact ConcreteCategory.congr_hom eq x
  let l (U : Cᵒᵖ) (x : W.obj.obj (I.op.obj U)) : P.obj.obj (I.op.obj U) :=
    Classical.choose ((he U (k.hom.app (I.op.obj U) x)).mp (hzero U x))
  have hl (U : Cᵒᵖ) (x : W.obj.obj (I.op.obj U)) :
      a.hom.app (I.op.obj U) (l U x) = k.hom.app (I.op.obj U) x :=
    Classical.choose_spec ((he U (k.hom.app (I.op.obj U) x)).mp (hzero U x))
  let α : I.op ⋙ W.obj ⟶ I.op ⋙ P.obj :=
    { app U := AddCommGrpCat.ofHom
        { toFun := l U
          map_zero' := by
            apply ha U
            rw [hl, map_zero, map_zero]
          map_add' := fun x y ↦ by
            apply ha U
            change a.hom.app (I.op.obj U) (l U (x + y)) =
              a.hom.app (I.op.obj U) (l U x + l U y)
            calc
              _ = k.hom.app (I.op.obj U) (x + y) := hl U _
              _ = k.hom.app (I.op.obj U) x + k.hom.app (I.op.obj U) y :=
                (k.hom.app (I.op.obj U)).hom.map_add x y
              _ = a.hom.app (I.op.obj U) (l U x) + a.hom.app (I.op.obj U) (l U y) := by
                rw [hl U x, hl U y]
              _ = _ := ((a.hom.app (I.op.obj U)).hom.map_add (l U x) (l U y)).symm }
      naturality {U V} f := by
        apply ConcreteCategory.hom_ext
        intro x
        let F := I.op.map f
        change l V (W.obj.map F x) = P.obj.map F (l U x)
        apply ha V
        calc
          _ = k.hom.app (I.op.obj V) (W.obj.map F x) := hl V _
          _ = Q.obj.map F (k.hom.app (I.op.obj U) x) :=
            ConcreteCategory.congr_hom (k.hom.naturality F) x
          _ = Q.obj.map F (a.hom.app (I.op.obj U) (l U x)) := by rw [hl]
          _ = _ := (ConcreteCategory.congr_hom (a.hom.naturality F) (l U x)).symm }
  let lift : W ⟶ P := ⟨Functor.IsCoverDense.sheafHom α⟩
  have hlift := Functor.IsCoverDense.sheafHom_restrict_eq α
  refine ⟨lift, hom_ext J I ?_⟩
  intro U
  have hApp : lift.hom.app (I.op.obj U) = α.app U := NatTrans.congr_app hlift U
  change lift.hom.app (I.op.obj U) ≫ a.hom.app (I.op.obj U) = k.hom.app (I.op.obj U)
  rw [hApp]
  apply ConcreteCategory.hom_ext
  exact hl U

end ManuscriptAudit.DenseSheafKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DenseSheafKernel.hom_ext,
      ``ManuscriptAudit.DenseSheafKernel.isLimit] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
