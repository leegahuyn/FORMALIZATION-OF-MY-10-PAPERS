import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCechTerms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift

/-! Local bijectivity of a presheaf-to-sheaf comparison is actual
bijectivity on affine charts once the presheaf has descent for the
finite affine families defining the native topology there. -/

namespace ManuscriptAudit.ProetaleRawAffineComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineCoproduct (coproduct injection descent injection_descent descent_covers)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}}

private abbrev J := Scheme.ProEt.topology S
private abbrev G := AddCommGrpCat.{u + 1}

set_option maxHeartbeats 2300000 in
/-- Two different affine charts over an affine chart have an
actual affine fibre product in the native site. -/
theorem affine_pullback {X Y T : S.ProEt} (f : X ⟶ T) (g : Y ⟶ T)
    [IsAffine X.left] [IsAffine Y.left] [IsAffine T.left] :
    IsAffine (pullback f g).left := by
  let F := Scheme.ProEt.forget S ⋙ Over.forget S
  let P := cospan f g
  let D := P ⋙ F
  have h (i : WalkingCospan) : IsAffine (D.obj i) := by
    cases i with
    | left => exact inferInstanceAs (IsAffine X.left)
    | right => exact inferInstanceAs (IsAffine Y.left)
    | one => exact inferInstanceAs (IsAffine T.left)
  let E : WalkingCospan ⥤ AffineScheme.{u} :=
    { obj := fun i ↦ AffineScheme.mk (D.obj i) (h i)
      map := fun a ↦ InducedCategory.homMk (D.map a)
      map_id := fun i ↦ InducedCategory.hom_ext (D.map_id i)
      map_comp := fun a b ↦ InducedCategory.hom_ext (D.map_comp a b) }
  have he : E ⋙ AffineScheme.forgetToScheme = D := rfl
  let a := preservesLimitIso F P
  let b := (preservesLimitIso AffineScheme.forgetToScheme E).trans
    (HasLimit.isoOfNatIso (eqToIso he))
  letI : IsAffine (AffineScheme.forgetToScheme.obj (limit E)) := isAffine_affineScheme _
  exact IsAffine.of_isIso (a.hom ≫ b.inv)

/-- Only actual finite affine families of the native site occur here. -/
def AffineFamilyDescent (P : S.ProEtᵒᵖ ⥤ G.{u}) : Prop :=
  ∀ {T : S.ProEt} [IsAffine T.left] (n : ℕ) (V : Fin n → S.ProEt) (a : ∀ i, V i ⟶ T),
    (∀ i, IsAffine (V i).left) → (∀ i, WeaklyEtale (a i).left) →
    (∀ x : T.left, ∃ i, ∃ y : (V i).left, (a i).left y = x) →
    Presieve.IsSheafFor (P ⋙ CategoryTheory.forget G.{u}) (Presieve.ofArrows V a)

private theorem map_map {P : S.ProEtᵒᵖ ⥤ G.{u}} {U V W : S.ProEt}
    (a : U ⟶ V) (b : V ⟶ W) (x : P.obj (op W)) :
    P.map a.op (P.map b.op x) = P.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private theorem nat_apply {P Q : S.ProEtᵒᵖ ⥤ G.{u}} (η : P ⟶ Q)
    {U V : S.ProEt} (a : U ⟶ V) (x : P.obj (op V)) :
    η.app (op U) (P.map a.op x) = Q.map a.op (η.app (op V) x) :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (η.naturality a.op)) x

variable {P : S.ProEtᵒᵖ ⥤ G.{u}} {F : Sheaf (J (S := S)) G.{u}}
  (η : P ⟶ F.obj) (hP : AffineFamilyDescent P)

set_option maxHeartbeats 2700000 in
/-- The local equality in the unit is global on each actual affine chart. -/
theorem injective_app [Presheaf.IsLocallyInjective (J (S := S)) η]
    (T : S.ProEt) [IsAffine T.left] : Function.Injective (η.app (op T)) := by
  intro x y he
  let R : Sieve T := Presheaf.equalizerSieve x y
  have hR : R ∈ J (S := S) T := Presheaf.equalizerSieve_mem (J (S := S)) η x y he
  obtain ⟨n, V, a, hV, hw, hm, hc⟩ := ProetaleAffineCover.exists_finite_refinement R hR
  apply (hP n V a hV hw hc).isSeparatedFor.ext
  rintro W _ ⟨i⟩
  exact hm i

set_option maxHeartbeats 5200000 in
/-- Compatible local lifts glue, and the sheafified unit therefore
gives the actual affine section isomorphism. -/
theorem surjective_app [Presheaf.IsLocallyInjective (J (S := S)) η]
    [Presheaf.IsLocallySurjective (J (S := S)) η]
    (T : S.ProEt) [IsAffine T.left] : Function.Surjective (η.app (op T)) := by
  classical
  intro x
  let R : Sieve T := Presheaf.imageSieve η x
  have hR : R ∈ J (S := S) T := Presheaf.imageSieve_mem (J (S := S)) η x
  obtain ⟨n, V, a, hV, hw, hm, hc⟩ := ProetaleAffineCover.exists_finite_refinement R hR
  letI := hV
  have h (i : Fin n) : ∃ y : P.obj (op (V i)), η.app (op (V i)) y = F.obj.map (a i).op x := hm i
  choose y hy using h
  let P₀ := P ⋙ CategoryTheory.forget G.{u}
  have hY : Presieve.Arrows.Compatible P₀ a y := by
    intro i j W b c he
    let q := pullback.fst (a i) (a j)
    let r := pullback.snd (a i) (a j)
    have hqr : q ≫ a i = r ≫ a j := pullback.condition
    letI : IsAffine (pullback (a i) (a j)).left := affine_pullback (a i) (a j)
    have hEq : P.map q.op (y i) = P.map r.op (y j) := by
      apply injective_app η hP (pullback (a i) (a j))
      rw [nat_apply, nat_apply, hy, hy, map_map, map_map, hqr]
    let k := pullback.lift b c he
    have hb : k ≫ q = b := pullback.lift_fst _ _ _
    have hc' : k ≫ r = c := pullback.lift_snd _ _ _
    change P.map b.op (y i) = P.map c.op (y j)
    exact (congrArg (fun e ↦ P.map e.op (y i)) hb).symm.trans
      ((map_map k q (y i)).symm.trans
        ((congrArg (P.map k.op) hEq).trans
          ((map_map k r (y j)).trans (congrArg (fun e ↦ P.map e.op (y j)) hc'))))
  obtain ⟨t, ht, _⟩ :=
    (Presieve.isSheafFor_arrows_iff (P := P₀) a).mp (hP n V a hV hw hc) y hY
  let d := descent V a
  have hd : F.obj.map d.op (η.app (op T) t) = F.obj.map d.op x := by
    let w := F.obj.map d.op x
    obtain ⟨s, _, hs⟩ := ProetaleAffineSingletonLift.glue_sections V F
      (fun i ↦ F.obj.map (injection V i).op w)
    have hv (i : Fin n) :
        F.obj.map (injection V i).op (F.obj.map d.op (η.app (op T) t)) =
          F.obj.map (injection V i).op w := by
      change _ = F.obj.map (injection V i).op (F.obj.map d.op x)
      rw [map_map, map_map, injection_descent, ← nat_apply, ht, hy]
    exact (hs _ hv).trans ((hs w (fun _ ↦ rfl)).symm)
  let F₀ := F.obj ⋙ CategoryTheory.forget G.{u}
  letI : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget G.{u}) :=
    AddCommGrpCat.adj.rightAdjoint_preservesLimits
  have hF : Presieve.IsSheaf (J (S := S)) F₀ :=
    (isSheaf_iff_isSheaf_of_type (J (S := S)) _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget G.{u}) F.property)
  have hD : Presieve.IsSheafFor F₀ (Presieve.singleton d) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hF.isSheafFor _ (descent_covers V a hw hc))
  refine ⟨t, hD.isSeparatedFor.ext ?_⟩
  rintro W _ ⟨rfl⟩
  exact hd

end
end ManuscriptAudit.ProetaleRawAffineComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleRawAffineComparison.affine_pullback,
      ``ManuscriptAudit.ProetaleRawAffineComparison.injective_app,
      ``ManuscriptAudit.ProetaleRawAffineComparison.surjective_app] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
