import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleSheaf

/-!
# The categorical coproduct of the finite-support sheaves

The component inclusions and sum of the component homomorphisms
give the actual coproduct universal property on the affine étale site.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace Presheaves

variable {C : Type u} [Category.{v} C] {I : Type}
variable (P : I → Cᵒᵖ ⥤ AddCommGrpCat.{0})

private def injection (i : I) : P i ⟶ directSum P where
  app X := by
    classical
    exact AddCommGrpCat.ofHom (DFinsupp.singleAddHom (fun a ↦ (P a).obj X) i)
  naturality _ _ f := by
    classical
    apply ConcreteCategory.hom_ext
    intro x
    change DFinsupp.single i ((P i).map f x) =
      DFinsupp.mapRange (fun a ↦ ((P a).map f).hom)
        (fun a ↦ ((P a).map f).hom.map_zero) (DFinsupp.single i x)
    rw [DFinsupp.mapRange_single]

private def desc {Q : Cᵒᵖ ⥤ AddCommGrpCat.{0}} (f : ∀ i, P i ⟶ Q) : directSum P ⟶ Q where
  app X := by
    classical
    exact AddCommGrpCat.ofHom (DFinsupp.sumAddHom fun a ↦ ((f a).app X).hom)
  naturality {X Y} g := by
    classical
    apply AddCommGrpCat.hom_ext
    apply DFinsupp.addHom_ext
    intro a x
    change DFinsupp.sumAddHom (fun b ↦ ((f b).app Y).hom)
        (DFinsupp.mapRange (fun b ↦ ((P b).map g).hom)
          (fun b ↦ ((P b).map g).hom.map_zero) (DFinsupp.single a x)) =
      Q.map g (DFinsupp.sumAddHom (fun b ↦ ((f b).app X).hom) (DFinsupp.single a x))
    rw [DFinsupp.mapRange_single, DFinsupp.sumAddHom_single, DFinsupp.sumAddHom_single]
    exact ConcreteCategory.congr_hom ((f a).naturality g) x

private theorem injection_desc {Q : Cᵒᵖ ⥤ AddCommGrpCat.{0}}
    (f : ∀ i, P i ⟶ Q) (i : I) : injection P i ≫ desc P f = f i := by
  classical
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro x
  change DFinsupp.sumAddHom (fun j ↦ ((f j).app X).hom) (DFinsupp.single i x) =
    ((f i).app X).hom x
  exact DFinsupp.sumAddHom_single (fun j ↦ ((f j).app X).hom) i x

private theorem desc_unique {Q : Cᵒᵖ ⥤ AddCommGrpCat.{0}}
    (f : ∀ i, P i ⟶ Q) (m : directSum P ⟶ Q) (hm : ∀ i, injection P i ≫ m = f i) :
    m = desc P f := by
  classical
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply DFinsupp.addHom_ext
  intro i x
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hm i) X) x
  change m.app X (DFinsupp.single i x) =
    DFinsupp.sumAddHom (fun j ↦ ((f j).app X).hom) (DFinsupp.single i x)
  rw [DFinsupp.sumAddHom_single]
  exact h

end Presheaves

open Presheaves

variable (S : Scheme.{u}) {I : Type}
variable (P : I → Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0})

/-- The actual inclusions in the finite-support sheaf. -/
def summand (i : I) : P i ⟶ affineEtaleDirectSum S P :=
  ⟨injection (fun j ↦ (P j).obj) i⟩

/-- The finite-support sheaf realizes the categorical coproduct on the affine étale site. -/
def affineEtaleDirectSumIsColimit : IsColimit (Cofan.mk (affineEtaleDirectSum S P) (summand S P)) :=
  Cofan.IsColimit.mk _
    (fun c ↦ ⟨desc (fun i ↦ (P i).obj) (fun i ↦ (c.inj i).hom)⟩)
    (fun c i ↦ Sheaf.hom_ext (injection_desc _ _ i))
    (fun c m hm ↦ Sheaf.hom_ext (desc_unique _ _ m.hom
      (fun i ↦ congrArg (fun f : P i ⟶ c.pt ↦ f.hom) (hm i))))

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.FiniteSupportPresheaf.affineEtaleDirectSumIsColimit
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
