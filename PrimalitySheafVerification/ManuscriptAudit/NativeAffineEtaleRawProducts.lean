import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleProductStages

/-! The raw section functor takes the actual finite disjoint unions
of affine charts to products. Both gluing and equality use actual
affine étale product stages. -/

namespace ManuscriptAudit.NativeAffineEtaleRawProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleStageCategory (Stage)
open NativeAffineEtaleStageSections (sectionDiagram etaleObject etaleMap)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements
  (chartMap stageAfterMap rawSection_map exists_representative exists_equal_representatives)
open NativeAffineEtaleProductStages (productStage projectionStageMap assemble component_assemble)
open NativeEtaleProductStageGluing (existsUnique_sections component)
open NativeAffineEtaleKanComparison (raw)
open ProetaleAffineTensor (structureMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
  (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  [∀ i, WeaklyEtale (structureMap A (B i))] [WeaklyEtale (structureMap A (∀ i, B i))]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private abbrev S (D : Type u) [CommRing D] [Algebra A D] [WeaklyEtale (structureMap A D)] :=
  (raw (X (A := A)) I).obj (op (ProetaleAffineTensor.object A D))

private abbrev F (D : Type u) [CommRing D] [Algebra A D] :=
  sectionDiagram (B := D) I

private abbrev incl {D : Type u} [CommRing D] [Algebra A D] [WeaklyEtale (structureMap A D)]
    (T : Stage A D) :=
  (rawSectionCocone (B := D) I).ι.app T

private abbrev restrict (i : ι) :=
  (raw (X (A := A)) I).map (chartMap (Pi.evalAlgHom A B i)).op

private theorem repr_natural {D : Type u} [CommRing D] [Algebra A D]
    [WeaklyEtale (structureMap A D)] {T U : Stage A D} (a : T ⟶ U)
    (x : (F I D).obj T) :
    incl I U ((F I D).map a x) = incl I T x :=
  DFunLike.congr_fun
    (congrArg AddCommGrpCat.Hom.hom ((rawSectionCocone (B := D) I).w a)) x

private theorem restrict_repr (i : ι) (T : Stage A (∀ j, B j))
    (x : (F I (∀ j, B j)).obj T) :
    restrict B I i (incl I T x) =
      incl I (stageAfterMap (Pi.evalAlgHom A B i) T) x :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (rawSection_map I (Pi.evalAlgHom A B i) T)) x

set_option maxHeartbeats 4200000 in
private theorem exists_glue (x : ∀ i, S I (B i)) :
    ∃ y : S I (∀ i, B i), ∀ i, restrict B I i y = x i := by
  classical
  have h (i : ι) : ∃ (T : Stage A (B i)) (v : (F I (B i)).obj T), incl I T v = x i :=
    exists_representative I (x i)
  choose T v hv using h
  let C (i : ι) := (T i).carrier
  let U := productStage B T
  obtain ⟨z, hz, _⟩ := existsUnique_sections I C v
  refine ⟨incl I U z, fun i ↦ ?_⟩
  rw [restrict_repr]
  let a := projectionStageMap B T i
  have hz' : (F I (B i)).map a z = v i := hz i
  exact (repr_natural I a z).symm.trans
    ((congrArg (incl I (T i)) hz').trans (hv i))

set_option maxHeartbeats 5500000 in
private theorem eq_of_equal_restrictions {x y : S I (∀ i, B i)}
    (hxy : ∀ i, restrict B I i x = restrict B I i y) : x = y := by
  classical
  obtain ⟨T, v, hv⟩ := exists_representative I x
  obtain ⟨U, w, hw⟩ := exists_representative I y
  let P (i : ι) := stageAfterMap (Pi.evalAlgHom A B i) T
  let Q (i : ι) := stageAfterMap (Pi.evalAlgHom A B i) U
  have he (i : ι) : incl I (P i) v = incl I (Q i) w := by
    rw [← restrict_repr, ← restrict_repr, hv, hw]
    exact hxy i
  have h (i : ι) : ∃ (V : Stage A (B i)) (a : P i ⟶ V) (b : Q i ⟶ V),
    (F I (B i)).map a v = (F I (B i)).map b w :=
    exists_equal_representatives I (P i) (Q i) v w (he i)
  choose V a b hab using h
  let M := productStage B V
  let p : T ⟶ M := assemble B V a
  let q : U ⟶ M := assemble B V b
  let s := (F I (∀ i, B i)).map p v
  let t := (F I (∀ i, B i)).map q w
  let C (i : ι) := (V i).carrier
  have hs (i : ι) : I.obj.map (component (A := A) C i).op s = (F I (B i)).map (a i) v := by
    change I.obj.map (component (A := A) C i).op (I.obj.map (etaleMap p).op v) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
      (congrArg (fun g ↦ I.obj.map g.op) (component_assemble B V a i))) v
  have ht (i : ι) : I.obj.map (component (A := A) C i).op t = (F I (B i)).map (a i) v := by
    change I.obj.map (component (A := A) C i).op (I.obj.map (etaleMap q).op w) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact (DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
      (congrArg (fun g ↦ I.obj.map g.op) (component_assemble B V b i))) w).trans (hab i).symm
  obtain ⟨z, _, hZ⟩ := existsUnique_sections I C
    (fun i ↦ (F I (B i)).map (a i) v)
  have hst : s = t := (hZ s hs).trans (hZ t ht).symm
  calc
    x = incl I T v := hv.symm
    _ = incl I M s := (repr_natural I p v).symm
    _ = incl I M t := congrArg (incl I M) hst
    _ = incl I U w := repr_natural I q w
    _ = y := hw

/-- The actual raw sections on a finite product chart are exactly
the product of the sections on its actual components. -/
theorem existsUnique_sections_raw (x : ∀ i, S I (B i)) :
    ∃! y : S I (∀ i, B i), ∀ i, restrict B I i y = x i := by
  obtain ⟨y, hy⟩ := exists_glue B I x
  refine ⟨y, hy, fun z hz ↦ eq_of_equal_restrictions B I ?_⟩
  intro i
  exact (hz i).trans (hy i).symm

end
end ManuscriptAudit.NativeAffineEtaleRawProducts

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineEtaleRawProducts.existsUnique_sections_raw
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
