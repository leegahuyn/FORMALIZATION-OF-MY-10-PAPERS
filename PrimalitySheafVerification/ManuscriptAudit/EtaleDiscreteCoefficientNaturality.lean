import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf

/-! The native small-étale constant-to-continuous comparison is natural in discrete coefficients. -/

namespace ManuscriptAudit.EtaleDiscreteCoefficientNaturality

open AlgebraicGeometry CategoryTheory
open EtaleContinuousMapSheaf (continuousMapSheaf constantSheafContinuousMapIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (X : Scheme.{u})
variable {M N : AddCommGrpCat.{u}} [TopologicalSpace M] [TopologicalSpace N]
    [DiscreteTopology M] [DiscreteTopology N] [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]

/-- The native arrow of continuous-map sheaves induced by a discrete coefficient homomorphism. -/
def map (f : M ⟶ N) : continuousMapSheaf X M ⟶ continuousMapSheaf X N where
  hom :=
    { app := fun W ↦ AddCommGrpCat.ofHom
        { toFun := fun a ↦ ⟨fun x ↦ f (a x), continuous_of_discreteTopology.comp a.continuous⟩
          map_zero' := by
            apply ContinuousMap.ext
            intro x
            exact map_zero f.hom
          map_add' := fun a b ↦ by
            apply ContinuousMap.ext
            intro x
            exact map_add f.hom (a x) (b x) }
      naturality := fun W W' g ↦ by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro a
        apply ContinuousMap.ext
        intro x
        rfl }

private def constArrow (B : AddCommGrpCat.{u}) [TopologicalSpace B] [DiscreteTopology B]
    [IsTopologicalAddGroup B] :
    (Functor.const (X.Etaleᵒᵖ)).obj B ⟶ (continuousMapSheaf X B).obj where
  app W := AddCommGrpCat.ofHom
    { toFun := ContinuousMap.const W.unop.left
      map_zero' := by ext w; rfl
      map_add' := by intros; ext w; rfl }
  naturality := by
    intro W W' f
    ext a
    rfl

private theorem constArrow_natural (f : M ⟶ N) :
    (Functor.const (X.Etaleᵒᵖ)).map f ≫ constArrow X N = constArrow X M ≫ (map X f).hom := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ContinuousMap.ext
  intro x
  rfl

/-- The actual comparison with continuous sections commutes with every native coefficient map. -/
theorem constantIso_natural (f : M ⟶ N) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map f ≫
      (constantSheafContinuousMapIso X N).hom =
    (constantSheafContinuousMapIso X M).hom ≫ map X f := by
  let P := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let c := Functor.const (X.Etaleᵒᵖ)
  have h₁ : P.map (c.map f) ≫ P.map (constArrow X N) =
      P.map (constArrow X M) ≫ P.map (map X f).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg P.map (constArrow_natural X f)
  have h₂ : P.map (map X f).hom ≫ (sheafificationIso (continuousMapSheaf X N)).inv =
      (sheafificationIso (continuousMapSheaf X M)).inv ≫ map X f :=
    (sheafificationNatIso X.smallEtaleTopology AddCommGrpCat.{u}).inv.naturality (map X f)
  change P.map (c.map f) ≫ (P.map (constArrow X N) ≫ (sheafificationIso (continuousMapSheaf X N)).inv) =
    (P.map (constArrow X M) ≫ (sheafificationIso (continuousMapSheaf X M)).inv) ≫ map X f
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

end
end ManuscriptAudit.EtaleDiscreteCoefficientNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleDiscreteCoefficientNaturality.map, ``ManuscriptAudit.EtaleDiscreteCoefficientNaturality.constantIso_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
