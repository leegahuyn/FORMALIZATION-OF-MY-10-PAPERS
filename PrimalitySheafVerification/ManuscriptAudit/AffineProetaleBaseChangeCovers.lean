import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineProetaleSite
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteAffineCover

/-! Surjective base change between affine schemes preserves and reflects
covering sieves on the actual affine pro-étale subsites. -/

namespace ManuscriptAudit.AffineProetaleBaseChangeCovers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineProetaleSite (Affine topology inclusion baseChange baseChange_comp_inclusion)

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
variable (f : X ⟶ Y)

private abbrev B := ProetaleBaseChange.baseChange f
private abbrev F := inclusion Y ⋙ B f

private theorem map_left_fst {U V : Y.ProEt} (a : U ⟶ V) :
    ((B f).map a).left ≫ pullback.fst V.hom f = pullback.fst U.hom f ≫ a.left := by
  simp only [B, ProetaleBaseChange.baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]

set_option maxHeartbeats 1200000 in
/-- A cover by images of original affine charts descends along the actual surjective base change. -/
theorem reflects_covering [Surjective f] {U : Affine Y} (R : Sieve U)
    (hR : R.functorPushforward (baseChange f) ∈ topology X ((baseChange f).obj U)) :
    R ∈ topology Y U := by
  classical
  let G := F f
  have hx := ((inclusion X).functorPushforward_mem_iff (topology X) (Scheme.ProEt.topology X)).mpr hR
  rw [← Sieve.functorPushforward_comp] at hx
  change R.functorPushforward G ∈ Scheme.ProEt.topology X (G.obj U) at hx
  letI : IsAffine (G.obj U).left := ((baseChange f).obj U).property
  obtain ⟨n, V, a, _, _, ha, hSurj⟩ :=
    ProetaleAffineCover.exists_finite_refinement (T := G.obj U) (R.functorPushforward G) hx
  have dat (i : Fin n) :
      ∃ (W : Affine Y) (b : W ⟶ U) (c : V i ⟶ G.obj W), R b ∧ a i = c ≫ G.map b :=
    ha i
  choose W b c hb hc using dat
  let D (i : Fin n) := (W i).obj
  let d (i : Fin n) : D i ⟶ U.obj := (inclusion Y).map (b i)
  let q := pullback.fst U.obj.hom f
  let hq : Surjective q := MorphismProperty.pullback_fst (P := @Surjective) U.obj.hom f inferInstance
  have ho (y : U.obj.left) : ∃ i, ∃ x : (D i).left, (d i).left x = y := by
    obtain ⟨z, hz⟩ := hq.surj y
    obtain ⟨i, x, hix⟩ := hSurj z
    let v := (c i).left x
    have e := congrArg (fun g : V i ⟶ G.obj U ↦ g.left x) (hc i)
    change (a i).left x = ((B f).map (d i)).left v at e
    have hd := congrArg
      (fun g : pullback (D i).hom f ⟶ U.obj.left ↦ g v) (map_left_fst f (d i))
    change q (((B f).map (d i)).left v) = (d i).left (pullback.fst (D i).hom f v) at hd
    refine ⟨i, pullback.fst (D i).hom f v, ?_⟩
    exact hd.symm.trans ((congrArg (fun s ↦ q s) (e.symm.trans hix)).trans hz)
  letI : IsAffine U.obj.left := U.property
  apply ((inclusion Y).functorPushforward_mem_iff (topology Y) (Scheme.ProEt.topology Y)).mp
  apply (Scheme.ProEt.topology Y).superset_covering _
    (ProetaleFiniteAffineCover.covering D d (fun i ↦ (W i).property) ho)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  exact ⟨W i, b i, 𝟙 _, hb i, by simp [d]⟩

/-- An original affine covering remains a native covering after base change. -/
theorem preserves_covering {U : Affine Y} (R : Sieve U)
    (hR : R ∈ topology Y U) :
    R.functorPushforward (baseChange f) ∈ topology X ((baseChange f).obj U) := by
  apply ((inclusion X).functorPushforward_mem_iff (topology X) (Scheme.ProEt.topology X)).mp
  rw [← Sieve.functorPushforward_comp]
  change R.functorPushforward (F f) ∈ Scheme.ProEt.topology X ((F f).obj U)
  rw [Sieve.functorPushforward_comp]
  exact (ProetaleBaseChange.coverPreserving f).cover_preserve
    (((inclusion Y).functorPushforward_mem_iff (topology Y) (Scheme.ProEt.topology Y)).mpr hR)

/-- Actual affine base change preserves and reflects the full covering relation. -/
theorem covering_iff [Surjective f] {U : Affine Y} (R : Sieve U) :
    R.functorPushforward (baseChange f) ∈ topology X ((baseChange f).obj U) ↔
      R ∈ topology Y U :=
  ⟨reflects_covering f R, preserves_covering f R⟩

end
end ManuscriptAudit.AffineProetaleBaseChangeCovers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineProetaleBaseChangeCovers.reflects_covering,
      ``ManuscriptAudit.AffineProetaleBaseChangeCovers.preserves_covering,
      ``ManuscriptAudit.AffineProetaleBaseChangeCovers.covering_iff] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
