import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageSeparatedRefinement
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawStageElements
import PrimalitySheafVerification.ManuscriptAudit.NativeEtaleSingletonSectionGluing
import PrimalitySheafVerification.ManuscriptAudit.NativeEtaleProductStageGluing

/-! Raw actual affine stages detect equality after every actual
surjective chart map, by a genuine affine étale cover refinement. -/

namespace ManuscriptAudit.NativeAffineEtaleRawSingletonSeparated

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap specMap)
open AffineEtaleStageCategory (Stage hom)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open NativeAffineEtaleStageSections (sectionDiagram etaleMap)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements
  (chartMap stageAfterMap rawSection_map exists_representative exists_equal_representatives)
open NativeAffineEtaleKanComparison (raw)
open NativeEtaleProductStageGluing (objectOf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

private abbrev algMap {C V : Type u} [CommRing C] [CommRing V]
    [Algebra A C] [Algebra A V] [Algebra.Etale A C] [Algebra.Etale A V]
    (f : C →ₐ[A] V) : objectOf (A := A) V ⟶ objectOf (A := A) C :=
  MorphismProperty.Over.homMk (specMap A f) (ProetaleAffineTensor.specMap_structureMap A f)

private theorem algMap_comp {C V W : Type u} [CommRing C] [CommRing V] [CommRing W]
    [Algebra A C] [Algebra A V] [Algebra A W]
    [Algebra.Etale A C] [Algebra.Etale A V] [Algebra.Etale A W]
    (f : C →ₐ[A] V) (g : V →ₐ[A] W) :
    algMap g ≫ algMap f = algMap (g.comp f) := by
  apply MorphismProperty.Over.Hom.ext
  change specMap A g ≫ specMap A f = specMap A (g.comp f)
  rw [← Spec.map_comp] <;> rfl

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private theorem restrict_restrict {W V U : (X (A := A)).Etale} (f : W ⟶ V) (g : V ⟶ U)
    (x : I.obj.obj (op U)) :
    I.obj.map f.op (I.obj.map g.op x) = I.obj.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private theorem sheaf_separated {V U : (X (A := A)).Etale} (f : V ⟶ U)
    (h : Function.Surjective f.left) : Function.Injective (I.obj.map f.op) := by
  intro x y he
  let t := I.obj.map f.op x
  let p := pullback.fst f f
  let q := pullback.snd f f
  have hMatch : I.obj.map p.op t = I.obj.map q.op t := by
    change I.obj.map p.op (I.obj.map f.op x) = I.obj.map q.op (I.obj.map f.op x)
    rw [restrict_restrict, restrict_restrict]
    exact congrArg (fun m : pullback f f ⟶ U ↦ I.obj.map m.op x) pullback.condition
  obtain ⟨w, _, hW⟩ := NativeEtaleSingletonSectionGluing.existsUnique_glue I f p q
    (IsPullback.of_hasPullback f f) h t hMatch
  exact (hW x rfl).trans (hW y he.symm).symm

variable {B D : Type u} [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A D)]

private abbrev repr {B : Type u} [CommRing B] [Algebra A B] [WeaklyEtale (structureMap A B)]
    (T : Stage A B) :=
  (rawSectionCocone (B := B) I).ι.app T

private theorem repr_natural {B : Type u} [CommRing B] [Algebra A B]
    [WeaklyEtale (structureMap A B)] {T U : Stage A B} (f : T ⟶ U)
    (x : (sectionDiagram (B := B) I).obj T) :
    repr I U ((sectionDiagram I).map f x) = repr I T x :=
  DFunLike.congr_fun
    (congrArg AddCommGrpCat.Hom.hom ((rawSectionCocone (B := B) I).w f)) x

set_option maxHeartbeats 8500000 in
/-- The actual raw section restriction is injective over a surjective
map of affine native charts as soon as the actual target chart is
covered by its finite étale approximations. -/
theorem restrict_injective (hApprox : FiniteTupleApproximation A B)
    (k : B →ₐ[A] D) (hCov : Function.Surjective (specMap A k)) :
    Function.Injective ((raw (X (A := A)) I).map (chartMap k).op) := by
  intro x y he
  obtain ⟨T, a, ha⟩ := exists_representative I x
  obtain ⟨U, b, hb⟩ := exists_representative I y
  let W := IsFiltered.max T U
  let t := IsFiltered.leftToMax T U
  let u := IsFiltered.rightToMax T U
  let s := (sectionDiagram I).map t a
  let z := (sectionDiagram I).map u b
  have hs : repr I W s = x := (repr_natural I t a).trans ha
  have hz : repr I W z = y := (repr_natural I u b).trans hb
  let d := stageAfterMap k W
  have h₁ (c : (sectionDiagram (B := B) I).obj W) :
      (raw (X (A := A)) I).map (chartMap k).op (repr I W c) = repr I d c :=
    DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (rawSection_map I k W)) c
  have hEq : repr I d s = repr I d z := by rw [← h₁, ← h₁, hs, hz, he]
  obtain ⟨N, p, q, h⟩ := exists_equal_representatives I d d s z hEq
  have hp₀ : N.toChart.comp (hom p) = k.comp W.toChart := p.property
  have hq₀ : N.toChart.comp (hom q) = k.comp W.toChart := q.property
  obtain ⟨Z, hZR, hZA, hZE, l, g, hZ, V, hVR, hVA, hVE, e, j, hSurj, hp, hq⟩ :=
    AffineEtaleStageSeparatedRefinement.exists_cover_refinement (C := W.carrier) (N := N.carrier)
      hApprox W.toChart (hom p) (hom q) N.toChart k hp₀ hq₀ hCov
  letI : CommRing Z := hZR
  letI : Algebra A Z := hZA
  letI : Algebra.Etale A Z := hZE
  letI : CommRing V := hVR
  letI : Algebra A V := hVA
  letI : Algebra.Etale A V := hVE
  let R := Stage.of A B g
  let m : W ⟶ R := ⟨l, hZ⟩
  have hMatch : (sectionDiagram I).map m s = (sectionDiagram I).map m z := by
    apply sheaf_separated I (algMap e) hSurj
    have hh := congrArg (I.obj.map (algMap j).op) h
    change I.obj.map (algMap j).op (I.obj.map (algMap (hom p)).op s) =
      I.obj.map (algMap j).op (I.obj.map (algMap (hom q)).op z) at hh
    rw [restrict_restrict, restrict_restrict, algMap_comp, algMap_comp, hp, hq] at hh
    change I.obj.map (algMap e).op (I.obj.map (algMap l).op s) =
      I.obj.map (algMap e).op (I.obj.map (algMap l).op z)
    simp only [restrict_restrict, algMap_comp]
    exact hh
  exact hs.symm.trans ((repr_natural I m s).symm.trans
    ((congrArg (repr I R) hMatch).trans ((repr_natural I m z).trans hz)))

end
end ManuscriptAudit.NativeAffineEtaleRawSingletonSeparated

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineEtaleRawSingletonSeparated.restrict_injective
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
