import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCategory
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageGlobalRelations

/-! When the actual chart has finite tuple approximation, its
canonical affine étale stage diagram has it as its actual ring colimit. -/

namespace ManuscriptAudit.AffineEtaleStageColimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage hom hom_toChart ringDiagram chartCocone)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

/-- Every finite tuple on B has preimages on one genuine affine
étale stage over A. -/
abbrev FiniteTupleApproximation (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ∀ {ι : Type u} [Finite ι] (w : ι → B),
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E),
      Algebra.Etale A E ∧ ∃ g : E →ₐ[A] B, ∀ i, ∃ x : E, g x = w i

variable (hApprox : FiniteTupleApproximation A B)

include hApprox in
private theorem exists_lift (b : B) : ∃ (X : Stage A B) (x : X.carrier), X.toChart x = b := by
  obtain ⟨C, hR, hA, hE, g, h⟩ := hApprox (fun _ : ULift.{u} Unit ↦ b)
  letI : CommRing C := hR
  letI : Algebra A C := hA
  letI : Algebra.Etale A C := hE
  obtain ⟨x, hx⟩ := h (ULift.up ())
  exact ⟨Stage.of A B g, x, hx⟩

/-- Equal chart values of two stage elements become equal at a
common actual étale stage. -/
include hApprox in
theorem exists_equal_stage (X Y : Stage A B) (x : X.carrier) (y : Y.carrier)
    (h : X.toChart x = Y.toChart y) :
    ∃ (Z : Stage A B) (f : X ⟶ Z) (g : Y ⟶ Z), hom f x = hom g y := by
  let W := IsFiltered.max X Y
  let f := IsFiltered.leftToMax X Y
  let g := IsFiltered.rightToMax X Y
  let z := hom f x - hom g y
  have hz : W.toChart z = 0 := by
    change W.toChart (hom f x - hom g y) = 0
    rw [map_sub, hom_toChart f x, hom_toChart g y, h, sub_self]
  obtain ⟨Q, hR, hA, hE, q, l, hq, hZero⟩ :=
    AffineEtaleStageGlobalRelations.exists_refinement hApprox W.toChart
      (fun _ : ULift.{u} Unit ↦ z) (fun _ ↦ hz)
  letI : CommRing Q := hR
  letI : Algebra A Q := hA
  letI : Algebra.Etale A Q := hE
  let Z := Stage.of A B l
  let e : W ⟶ Z := ⟨q, hq⟩
  have he := hZero (ULift.up ())
  change q (hom f x - hom g y) = 0 at he
  rw [map_sub] at he
  exact ⟨Z, f ≫ e, g ≫ e, sub_eq_zero.mp he⟩

include hApprox in
private theorem exists_two_lifts (b c : B) :
    ∃ (X : Stage A B) (x y : X.carrier), X.toChart x = b ∧ X.toChart y = c := by
  obtain ⟨X, x, hx⟩ := exists_lift hApprox b
  obtain ⟨Y, y, hy⟩ := exists_lift hApprox c
  let f := IsFiltered.leftToMax X Y
  let g := IsFiltered.rightToMax X Y
  exact ⟨_, hom f x, hom g y, (hom_toChart f x).trans hx, (hom_toChart g y).trans hy⟩

include hApprox in
set_option maxHeartbeats 3200000 in
/-- The literal chart ring is the filtered colimit of its actual
affine étale stages, in commutative rings. -/
def isColimit_chart : IsColimit (chartCocone (A := A) (B := B)) := by
  classical
  let cc := chartCocone (A := A) (B := B)
  let X (b : B) := Classical.choose (exists_lift hApprox b)
  let x (b : B) : (X b).carrier := Classical.choose (Classical.choose_spec (exists_lift hApprox b))
  have hx (b : B) : (X b).toChart (x b) = b :=
    Classical.choose_spec (Classical.choose_spec (exists_lift hApprox b))
  have make (s : Cocone (ringDiagram (A := A) (B := B))) :
      ∃ m : cc.pt ⟶ s.pt, ∀ T, cc.ι.app T ≫ m = s.ι.app T := by
    let v (b : B) : s.pt := (s.ι.app (X b)).hom (x b)
    have hNat {T U : Stage A B} (f : T ⟶ U) (a : T.carrier) :
        (s.ι.app U).hom (hom f a) = (s.ι.app T).hom a :=
      congrArg (fun g : ringDiagram.obj T ⟶ s.pt ↦ g.hom a) (s.w f)
    have hLift (T : Stage A B) (a : T.carrier) : v (T.toChart a) = (s.ι.app T).hom a := by
      let b := T.toChart a
      obtain ⟨U, f, g, he⟩ := exists_equal_stage hApprox (X b) T (x b) a (hx b)
      calc
        _ = (s.ι.app U).hom (hom f (x b)) := (hNat f _).symm
        _ = (s.ι.app U).hom (hom g a) := congrArg (s.ι.app U).hom he
        _ = _ := hNat g a
    let base := Stage.of A B (Algebra.ofId A B)
    let m : B →+* s.pt :=
      { toFun := v
        map_one' := by simpa only [map_one] using hLift base 1
        map_zero' := by simpa only [map_zero] using hLift base 0
        map_mul' := by
          intro b c
          obtain ⟨T, a, d, ha, hd⟩ := exists_two_lifts hApprox b c
          calc
            v (b * c) = v (T.toChart (a * d)) := by rw [map_mul, ha, hd]
            _ = (s.ι.app T).hom (a * d) := hLift T (a * d)
            _ = _ := by rw [map_mul, ← hLift T a, ← hLift T d, ha, hd]
        map_add' := by
          intro b c
          obtain ⟨T, a, d, ha, hd⟩ := exists_two_lifts hApprox b c
          calc
            v (b + c) = v (T.toChart (a + d)) := by rw [map_add, ha, hd]
            _ = (s.ι.app T).hom (a + d) := hLift T (a + d)
            _ = _ := by rw [map_add, ← hLift T a, ← hLift T d, ha, hd] }
    refine ⟨CommRingCat.ofHom m, fun T ↦ CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)⟩
    exact hLift T a
  let desc (s : Cocone (ringDiagram (A := A) (B := B))) := Classical.choose (make s)
  have hDesc (s : Cocone (ringDiagram (A := A) (B := B))) (T : Stage A B) :
      cc.ι.app T ≫ desc s = s.ι.app T := Classical.choose_spec (make s) T
  refine ⟨desc, hDesc, ?_⟩
  intro s m hm
  apply CommRingCat.hom_ext
  ext b
  obtain ⟨T, a, ha⟩ := exists_lift hApprox b
  have h := congrArg (fun g : ringDiagram.obj T ⟶ s.pt ↦ g.hom a)
    ((hm T).trans (hDesc s T).symm)
  change m.hom (T.toChart a) = (desc s).hom (T.toChart a) at h
  exact ha ▸ h

end
end ManuscriptAudit.AffineEtaleStageColimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageColimit.exists_equal_stage,
      ``ManuscriptAudit.AffineEtaleStageColimit.isColimit_chart] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
