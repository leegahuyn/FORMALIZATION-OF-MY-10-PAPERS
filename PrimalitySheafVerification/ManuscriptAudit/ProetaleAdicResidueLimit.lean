import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleResidueSheaves

/-! The actual pro-étale adic sheaf satisfies the native ordinary residue limit property. -/

namespace ManuscriptAudit.ProetaleAdicResidueLimit

open AlgebraicGeometry CategoryTheory Opposite
open ProetalePadicSectionTower
open ProetaleResidueSheaves (residueSheaf residueTransition residueReduction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev A := AddCommGrpCat.{0}

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]
variable (F : Sheaf (Scheme.ProEt.topology X) A)
variable (ρ : ∀ n, F ⟶ residueSheaf X ℓ n)
variable (hρ : ∀ n, ρ (n + 1) ≫ residueTransition X ℓ n = ρ n)

private def compatibleAt (W : X.ProEt) : F.obj.obj (op W) →+ compatibleSections ℓ W.left where
  toFun x := ⟨fun n ↦ (ρ n).hom.app (op W) x, fun n ↦
    CategoryTheory.congr_fun
      (congrArg (fun m : F ⟶ residueSheaf X ℓ n ↦ m.hom.app (op W)) (hρ n)) x⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero ((ρ n).hom.app (op W)).hom
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add ((ρ n).hom.app (op W)).hom x y

/-- A compatible family of actual residue sheaf arrows has a lift to the actual adic sheaf. -/
def lift : F ⟶ X.ellAdicSheaf ℓ where
  hom :=
    { app := fun W ↦ AddCommGrpCat.ofHom
        ((sheafSectionsEquiv ℓ X W.unop).symm.toAddMonoidHom.comp
          (compatibleAt X ℓ F ρ hρ W.unop))
      naturality := fun U V g ↦ by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        let a := sheafSectionsEquiv ℓ X U.unop
        let b := sheafSectionsEquiv ℓ X V.unop
        let z := a.symm (compatibleAt X ℓ F ρ hρ U.unop x)
        change b.symm (compatibleAt X ℓ F ρ hρ V.unop (F.obj.map g x)) =
          (X.ellAdicSheaf ℓ).obj.map g z
        apply b.injective
        rw [AddEquiv.apply_symm_apply]
        apply Subtype.ext
        funext n
        apply ContinuousMap.ext
        intro y
        change (compatibleAt X ℓ F ρ hρ V.unop (F.obj.map g x)).val n y =
          (sheafSectionsEquiv ℓ X V.unop ((X.ellAdicSheaf ℓ).obj.map g z)).val n y
        have hr := sheafSectionsEquiv_restrict ℓ X g.unop z n y
        change (sheafSectionsEquiv ℓ X V.unop ((X.ellAdicSheaf ℓ).obj.map g z)).val n y =
          (sheafSectionsEquiv ℓ X U.unop z).val n (g.unop.left y) at hr
        rw [hr]
        change (ρ n).hom.app V (F.obj.map g x) y = (a (a.symm _)).val n (g.unop.left y)
        rw [AddEquiv.apply_symm_apply]
        exact congrArg (fun f : C(V.unop.left, ZMod (ℓ ^ n)) ↦ f y)
          (CategoryTheory.congr_fun ((ρ n).hom.naturality g) x) }

theorem lift_comp (n : ℕ) : lift X ℓ F ρ hρ ≫ residueReduction X ℓ n = ρ n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  let e := sheafSectionsEquiv ℓ X W.unop
  change (e (e.symm (compatibleAt X ℓ F ρ hρ W.unop x))).val n = (ρ n).hom.app W x
  rw [AddEquiv.apply_symm_apply] <;> rfl

/-- The finite reductions jointly detect maps into the actual pro-étale adic sheaf. -/
theorem residue_hom_ext {a b : F ⟶ X.ellAdicSheaf ℓ}
    (h : ∀ n, a ≫ residueReduction X ℓ n = b ≫ residueReduction X ℓ n) : a = b := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change a.hom.app W x = b.hom.app W x
  apply (sheafSectionsEquiv ℓ X W.unop).injective
  apply Subtype.ext
  funext n
  exact CategoryTheory.congr_fun
    (congrArg (fun m : F ⟶ residueSheaf X ℓ n ↦ m.hom.app W) (h n)) x

include hρ in
/-- The native pro-étale adic sheaf is the ordinary limit of its actual residue sheaves. -/
theorem existsUnique_residueLift :
    ∃! (a : F ⟶ X.ellAdicSheaf ℓ), ∀ n, a ≫ residueReduction X ℓ n = ρ n :=
  ⟨lift X ℓ F ρ hρ, lift_comp X ℓ F ρ hρ, fun a ha ↦
    residue_hom_ext X ℓ F (fun n ↦ (ha n).trans (lift_comp X ℓ F ρ hρ n).symm)⟩

end
end ManuscriptAudit.ProetaleAdicResidueLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicResidueLimit.lift,
      ``ManuscriptAudit.ProetaleAdicResidueLimit.lift_comp,
      ``ManuscriptAudit.ProetaleAdicResidueLimit.residue_hom_ext,
      ``ManuscriptAudit.ProetaleAdicResidueLimit.existsUnique_residueLift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
