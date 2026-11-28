import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-! The genuine Mayer–Vietoris exact sequence reduces to restriction to
one chart if restriction from the other chart to the overlap is an isomorphism. -/

namespace ManuscriptAudit.MayerVietorisOneChart

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{w})

private abbrev fromLeft := ((F.cohomologyPresheaf 1).map S.f₁₂.op).hom
private abbrev fromRight := ((F.cohomologyPresheaf 1).map S.f₁₃.op).hom
private abbrev toLeft := ((F.cohomologyPresheaf 1).map S.f₂₄.op).hom

/-- The actual degree-one restriction from the whole object to the right chart. -/
abbrev toRight := ((F.cohomologyPresheaf 1).map S.f₃₄.op).hom

/-- If restriction from the left chart to the overlap is onto, each
degree-one class on the right chart lifts to the whole object. -/
theorem toRight_surjective (h : Function.Surjective (fromLeft S F)) :
    Function.Surjective (toRight S F) := by
  intro y
  obtain ⟨x, hx⟩ := h (fromRight S F y)
  let E := AddCommGrpCat.biprodIsoProd (F.H' 1 S.X₂) (F.H' 1 S.X₃)
  let z := E.inv (x, y)
  have hz : S.fromBiprod F 1 z = 0 := by
    change S.fromBiprod F 1 ((AddCommGrpCat.biprodIsoProd _ _).inv (x, y)) = 0
    rw [S.fromBiprod_biprodIsoProd_inv_apply]
    exact sub_eq_zero.mpr hx
  have he := (S.sequence_exact F 0 1 rfl).exact' 3 4 5
  rw [ShortComplex.ab_exact_iff_function_exact] at he
  obtain ⟨a, ha⟩ := (he z).1 hz
  refine ⟨a, ?_⟩
  have hP := congrArg (fun b => (E.hom b).2) ha
  change (E.hom (S.toBiprod F 1 a)).2 = (E.hom (E.inv (x, y))).2 at hP
  simp only [S.toBiprod_apply, E, Iso.inv_hom_id_apply] at hP
  exact hP

/-- If restriction from the left chart to the overlap is injective,
the kernel of restriction to the right chart is the actual boundary image. -/
theorem toRight_ker (h : Function.Injective (fromLeft S F)) :
    (toRight S F).ker = ((S.δ F 0 1 rfl).hom).range := by
  have he := ((S.sequence_exact F 0 1 rfl).exact' 2 3 4).ab_range_eq_ker
  rw [he]
  ext x
  change toRight S F x = 0 ↔ S.toBiprod F 1 x = 0
  let E := AddCommGrpCat.biprodIsoProd (F.H' 1 S.X₂) (F.H' 1 S.X₃)
  constructor
  · intro hx
    have hr : S.fromBiprod F 1 (S.toBiprod F 1 x) = 0 := by
      have e := S.toBiprod_fromBiprod F 1
      exact congrArg (fun f : F.H' 1 S.X₄ ⟶ F.H' 1 S.X₁ => f x) e
    rw [S.toBiprod_apply, S.fromBiprod_biprodIsoProd_inv_apply] at hr
    change fromLeft S F (toLeft S F x) - fromRight S F (toRight S F x) = 0 at hr
    rw [hx, map_zero, sub_zero] at hr
    have hz : toLeft S F x = 0 := h (hr.trans (map_zero (fromLeft S F)).symm)
    rw [S.toBiprod_apply]
    change E.inv (toLeft S F x, toRight S F x) = 0
    rw [hz, hx]
    exact map_zero E.inv.hom
  · intro hx
    have hn := congrArg (fun b => (E.hom b).2) hx
    rw [S.toBiprod_apply] at hn
    change (E.hom (E.inv (toLeft S F x, toRight S F x))).2 = (E.hom 0).2 at hn
    simp only [Iso.inv_hom_id_apply] at hn
    exact hn.trans (congrArg Prod.snd (map_zero E.hom.hom))

end

end ManuscriptAudit.MayerVietorisOneChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MayerVietorisOneChart.toRight_surjective,
      ``ManuscriptAudit.MayerVietorisOneChart.toRight_ker] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
