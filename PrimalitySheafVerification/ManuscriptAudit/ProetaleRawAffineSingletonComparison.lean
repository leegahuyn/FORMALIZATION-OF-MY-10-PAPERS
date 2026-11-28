import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleRawAffineComparison

/-! On the actual affine basis it suffices to glue on affine
singleton covers and take products over finite affine coproducts.
The local-to-global argument never replaces the native topology. -/

namespace ManuscriptAudit.ProetaleRawAffineSingletonComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineCoproduct
  (coproduct injection descent injection_descent descent_covers descent_weaklyEtale descent_surjective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}}

private abbrev J := Scheme.ProEt.topology S
private abbrev G := AddCommGrpCat.{u + 1}

/-- Sections over actual finite affine disjoint unions are
products of the actual component sections. -/
def AffineCoproductSections (P : S.ProEtᵒᵖ ⥤ G.{u}) : Prop :=
  ∀ (n : ℕ) (V : Fin n → S.ProEt), (∀ i, IsAffine (V i).left) →
    ∀ x : ∀ i, P.obj (op (V i)), ∃! y : P.obj (op (coproduct V)),
      ∀ i, P.map (injection V i).op y = x i

/-- Separation only on actual affine weakly étale singleton covers. -/
def AffineSingletonSeparated (P : S.ProEtᵒᵖ ⥤ G.{u}) : Prop :=
  ∀ {V T : S.ProEt} (f : V ⟶ T), IsAffine V.left → IsAffine T.left →
    WeaklyEtale f.left → Surjective f.left →
    Function.Injective (P.map f.op)

/-- Gluing only on actual affine weakly étale singleton covers. -/
def AffineSingletonGluing (P : S.ProEtᵒᵖ ⥤ G.{u}) : Prop :=
  ∀ {V T : S.ProEt} (f : V ⟶ T), IsAffine V.left → IsAffine T.left →
    WeaklyEtale f.left → Surjective f.left →
    ∀ x : P.obj (op V),
      P.map (pullback.fst f f).op x = P.map (pullback.snd f f).op x →
        ∃ y : P.obj (op T), P.map f.op y = x

private theorem map_map {P : S.ProEtᵒᵖ ⥤ G.{u}} {U V W : S.ProEt}
    (a : U ⟶ V) (b : V ⟶ W) (x : P.obj (op W)) :
    P.map a.op (P.map b.op x) = P.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private theorem nat_apply {P Q : S.ProEtᵒᵖ ⥤ G.{u}} (η : P ⟶ Q)
    {U V : S.ProEt} (a : U ⟶ V) (x : P.obj (op V)) :
    η.app (op U) (P.map a.op x) = Q.map a.op (η.app (op V) x) :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (η.naturality a.op)) x

variable {P : S.ProEtᵒᵖ ⥤ G.{u}} {F : Sheaf (J (S := S)) G.{u}} (η : P ⟶ F.obj)

set_option maxHeartbeats 3900000 in
/-- Separation on affine singletons and finite coproduct detection
convert the local injectivity of a sheafification map to injectivity
on each actual affine chart. -/
theorem injective_app [Presheaf.IsLocallyInjective (J (S := S)) η]
    (hProducts : AffineCoproductSections P) (hSep : AffineSingletonSeparated P)
    (T : S.ProEt) [IsAffine T.left] : Function.Injective (η.app (op T)) := by
  intro x y he
  let R : Sieve T := Presheaf.equalizerSieve x y
  have hR : R ∈ J (S := S) T := Presheaf.equalizerSieve_mem (J (S := S)) η x y he
  obtain ⟨n, V, a, hAff, hw, hm, hc⟩ := ProetaleAffineCover.exists_finite_refinement R hR
  letI := hAff
  let W := coproduct V
  let f := descent V a
  apply hSep f inferInstance inferInstance (descent_weaklyEtale V a hw) (descent_surjective V a hc)
  let z := P.map f.op y
  obtain ⟨t, _, ht⟩ := hProducts n V hAff (fun i ↦ P.map (injection V i).op z)
  have hx (i : Fin n) : P.map (injection V i).op (P.map f.op x) = P.map (injection V i).op z := by
    change _ = P.map (injection V i).op (P.map f.op y)
    rw [map_map, map_map, injection_descent]
    exact hm i
  exact (ht _ hx).trans (ht z (fun _ ↦ rfl)).symm

set_option maxHeartbeats 5200000 in
/-- The locally bijective comparison is surjective on actual affine
charts when their singleton covers have descent. -/
theorem surjective_app [Presheaf.IsLocallyInjective (J (S := S)) η]
    [Presheaf.IsLocallySurjective (J (S := S)) η]
    (hProducts : AffineCoproductSections P) (hSep : AffineSingletonSeparated P)
    (hGlue : AffineSingletonGluing P) (T : S.ProEt) [IsAffine T.left] :
    Function.Surjective (η.app (op T)) := by
  classical
  intro x
  let R : Sieve T := Presheaf.imageSieve η x
  have hR : R ∈ J (S := S) T := Presheaf.imageSieve_mem (J (S := S)) η x
  obtain ⟨n, V, a, hAff, hw, hm, hc⟩ := ProetaleAffineCover.exists_finite_refinement R hR
  letI := hAff
  let W := coproduct V
  let f := descent V a
  have h (i : Fin n) : ∃ y : P.obj (op (V i)), η.app (op (V i)) y = F.obj.map (a i).op x := hm i
  choose v hv using h
  obtain ⟨w, hw', _⟩ := hProducts n V hAff v
  have hηw : η.app (op W) w = F.obj.map f.op x := by
    let z := F.obj.map f.op x
    obtain ⟨t, _, ht⟩ := ProetaleAffineSingletonLift.glue_sections V F
      (fun i ↦ F.obj.map (injection V i).op z)
    have he (i : Fin n) : F.obj.map (injection V i).op (η.app (op W) w) =
        F.obj.map (injection V i).op z := by
      change _ = F.obj.map (injection V i).op (F.obj.map f.op x)
      rw [← nat_apply, hw', hv, map_map, injection_descent]
    exact (ht _ he).trans ((ht z (fun _ ↦ rfl)).symm)
  let q := pullback.fst f f
  let r := pullback.snd f f
  letI : IsAffine (pullback f f).left := ProetaleRawAffineComparison.affine_pullback f f
  have hqr : q ≫ f = r ≫ f := pullback.condition
  have hMatch : P.map q.op w = P.map r.op w := by
    apply injective_app η hProducts hSep (pullback f f)
    rw [nat_apply, nat_apply, hηw, map_map, map_map, hqr]
  obtain ⟨y, hy⟩ := hGlue f inferInstance inferInstance (descent_weaklyEtale V a hw)
    (descent_surjective V a hc) w hMatch
  have hEq : F.obj.map f.op (η.app (op T) y) = F.obj.map f.op x := by
    rw [← nat_apply, hy, hηw]
  let F₀ := F.obj ⋙ CategoryTheory.forget G.{u}
  letI : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget G.{u}) :=
    AddCommGrpCat.adj.rightAdjoint_preservesLimits
  have hF : Presieve.IsSheaf (J (S := S)) F₀ :=
    (isSheaf_iff_isSheaf_of_type (J (S := S)) _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget G.{u}) F.property)
  have hD : Presieve.IsSheafFor F₀ (Presieve.singleton f) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hF.isSheafFor _ (descent_covers V a hw hc))
  refine ⟨y, hD.isSeparatedFor.ext ?_⟩
  rintro Z _ ⟨rfl⟩
  exact hEq

end
end ManuscriptAudit.ProetaleRawAffineSingletonComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleRawAffineSingletonComparison.injective_app,
      ``ManuscriptAudit.ProetaleRawAffineSingletonComparison.surjective_app] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
