import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-! Genuine Mayer–Vietoris vanishing in degree one for a two-open cover. -/

namespace ManuscriptAudit.MayerVietorisHOneVanishing

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

private theorem fromBiprod_surjective
    (h : Function.Surjective ((F.cohomologyPresheaf 0).map S.f₁₂.op).hom) :
    Function.Surjective (S.fromBiprod F 0).hom := by
  intro y
  obtain ⟨x, hx⟩ := h y
  let E := AddCommGrpCat.biprodIsoProd (F.H' 0 S.X₂) (F.H' 0 S.X₃)
  refine ⟨E.inv (x, 0), ?_⟩
  change S.fromBiprod F 0 ((AddCommGrpCat.biprodIsoProd _ _).inv (x, 0)) = y
  rw [S.fromBiprod_biprodIsoProd_inv_apply, map_zero, sub_zero]
  exact hx

/-- If both native degree-one groups on the two opens vanish, and degree
zero on one open maps onto the overlap, the ambient degree-one group vanishes. -/
theorem subsingleton_HOne
    (h0 : Function.Surjective ((F.cohomologyPresheaf 0).map S.f₁₂.op).hom)
    (hL : Subsingleton (F.H' 1 S.X₂)) (hR : Subsingleton (F.H' 1 S.X₃)) :
    Subsingleton (F.H' 1 S.X₄) := by
  have he : (S.δ F 0 1 rfl).hom.range = (S.toBiprod F 1).hom.ker :=
    ((S.sequence_exact F 0 1 rfl).exact' 2 3 4).ab_range_eq_ker
  have hZero (x : F.H' 1 S.X₄) : x = 0 := by
    have hz : x ∈ (S.toBiprod F 1).hom.ker := by
      change S.toBiprod F 1 x = 0
      rw [S.toBiprod_apply]
      have hl : (F.cohomologyPresheaf 1).map S.f₂₄.op x = 0 := hL.allEq _ _
      have hr : (F.cohomologyPresheaf 1).map S.f₃₄.op x = 0 := hR.allEq _ _
      rw [hl, hr]
      exact map_zero (AddCommGrpCat.biprodIsoProd (F.H' 1 S.X₂) (F.H' 1 S.X₃)).inv.hom
    rw [← he] at hz
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨z, rfl⟩ := fromBiprod_surjective S F h0 y
    have H := S.fromBiprod_δ F 0 1 rfl
    exact ConcreteCategory.congr_hom H z
  exact ⟨fun x y => (hZero x).trans (hZero y).symm⟩

end

end ManuscriptAudit.MayerVietorisHOneVanishing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MayerVietorisHOneVanishing.subsingleton_HOne
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
