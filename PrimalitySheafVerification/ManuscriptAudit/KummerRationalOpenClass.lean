import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeUnitSections
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundary

/-! A coefficient-field unit with no dth root gives an actual ambient
Kummer class that remains nonzero on any open with a rational point. -/

namespace ManuscriptAudit.KummerRationalOpenClass

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open EtaleTwoOpenHOne (identityObject openArrow)
open KummerRelativeFull KummerRelativeUnitSections KummerUnitsSheaf
open SheafPresheafHOneBoundary

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] {X Y : Scheme.{0}}
variable (k : X ⟶ Spec (CommRingCat.of K))
variable (j : Y ⟶ X) [IsOpenImmersion j]

private abbrev C := AddCommGrpCat.{0}

/-- A genuine ambient Kummer class detected on an open which contains
a rational point over the coefficient field. -/
theorem exists_class_detected_on_open (p : Spec (CommRingCat.of K) ⟶ Y)
    (hp : p ≫ j ≫ k = 𝟙 _) (d : ℕ) (hd : 0 < d) [NeZero (d : K)] (u : Kˣ)
    (hu : ¬ ∃ v : Kˣ, v ^ d = u) :
    ∃ z : (sequence X d).X₁.H' 1 (identityObject X),
      ((sequence X d).X₁.cohomologyPresheaf 1).map (openArrow j).op z ≠ 0 := by
  let J := X.smallEtaleTopology
  let S := sequence X d
  let hS := sequence_shortExact k d hd
  let U := identityObject X
  let V := Scheme.Etale.mk j
  let a := openArrow j
  let E := (sheafToPresheaf J C).mapIso (unitsIso (X := X) d).symm
  let g := Scheme.ΓSpecIso (CommRingCat.of K)
  let c := g.inv ≫ k.appTop
  let r := p.appTop ≫ g.hom
  let t : S.X₃.obj.obj (op U) :=
    E.inv.app (op U) (ringUnits.map c (Additive.ofMul u))
  let t' : S.X₃.obj.obj (op V) := S.X₃.obj.map a.op t
  have hTriple : c ≫ j.appTop ≫ r = 𝟙 (CommRingCat.of K) := by
    calc
      _ = g.inv ≫ (p ≫ j ≫ k).appTop ≫ g.hom := by
        simp only [c, r, Scheme.Hom.comp_appTop, Category.assoc]
      _ = _ := by rw [hp]; simp
  have hUnit : ringUnits.map r (E.hom.app (op V) t') = Additive.ofMul u := by
    have hn := ConcreteCategory.congr_hom (E.hom.naturality a.op) t
    change E.hom.app (op V) t' =
      ringUnits.map j.appTop (E.hom.app (op U) t) at hn
    have ht : E.hom.app (op U) t = ringUnits.map c (Additive.ofMul u) :=
      (E.app (op U)).inv_hom_id_apply _
    rw [hn, ht, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← ringUnits.map_comp, ← ringUnits.map_comp, hTriple, ringUnits.map_id] <;> rfl
  refine ⟨boundaryOfSection J S hS U t, ?_⟩
  intro hz
  rw [boundaryOfSection_restrict J S hS a t] at hz
  obtain ⟨w, hw⟩ := (boundaryOfSection_eq_zero_iff J S hS V t').mp hz
  let w' : Additive (Γ(Y, ⊤))ˣ := E.hom.app (op V) w
  let v : Additive Kˣ := ringUnits.map r w'
  have hW : d • w' = E.hom.app (op V) t' := by
    change d • E.hom.app (op V) w = _
    rw [← map_nsmul]
    exact congrArg (fun y : S.X₂.obj.obj (op V) => E.hom.app (op V) y)
      ((coordinateUnitsIso_power (d := d) w).symm.trans hw)
  have hV : d • v = Additive.ofMul u := by
    change d • ringUnits.map r w' = _
    rw [← map_nsmul, hW, hUnit]
  exact hu ⟨v.toMul, congrArg (fun x : Additive Kˣ => x.toMul) hV⟩

end
end ManuscriptAudit.KummerRationalOpenClass

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.KummerRationalOpenClass.exists_class_detected_on_open
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
