import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeEtaleUnderRingGluing
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawStageElements

/-! A glued section on a literal finite stage supplies a raw
section on the actual base chart. -/

namespace ManuscriptAudit.NativeAffineRawGluedRepresentatives

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap)
open AffineEtaleStageCategory (Stage)
open NativeAffineEtaleStageSections (etaleObject etaleMap sectionDiagram)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements (chartMap stageAfterMap rawSection_map)
open NativeAffineEtaleKanComparison (raw)
open NativeEtaleUnderRingGluing (obj arrow)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev R := CommRingCat.of A
private abbrev X := spectrum A
private abbrev G := AddCommGrpCat.{u + 1}
private abbrev U (C : Type u) [CommRing C] [Algebra A C] :=
  CommRingCat.mkUnder (R (A := A)) C

/-- An étale ring object with an actual chart map supplies a stable stage. -/
abbrev stageOf {C : Type u} [CommRing C] [Algebra A C]
    (M : Under (R (A := A))) [Etale (Spec.map M.hom)] (f : M ⟶ U (A := A) C) : Stage A C := by
  letI : Algebra A M.right := M.hom.hom.toAlgebra
  have h : (algebraMap A M.right).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := M.hom)).mp
      (inferInstanceAs (Etale (Spec.map M.hom)))
  letI : Algebra.Etale A M.right := (RingHom.etale_algebraMap).mp h
  exact Stage.of A C (CommRingCat.toAlgHom f)

/-- The étale object of the stage is the literal spectrum over the base. -/
theorem etaleObject_stageOf {C : Type u} [CommRing C] [Algebra A C]
    (M : Under (R (A := A))) [Etale (Spec.map M.hom)] (f : M ⟶ U (A := A) C) :
    etaleObject (stageOf M f) = obj M := rfl

variable {B D : Type u} [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A D)]

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private abbrev incl {C : Type u} [CommRing C] [Algebra A C] [WeaklyEtale (structureMap A C)]
    (T : Stage A C) :=
  (rawSectionCocone (B := C) I).ι.app T

private theorem repr_natural {C : Type u} [CommRing C] [Algebra A C]
    [WeaklyEtale (structureMap A C)] {T V : Stage A C} (f : T ⟶ V)
    (x : (sectionDiagram (B := C) I).obj T) :
    incl I V ((sectionDiagram (B := C) I).map f x) = incl I T x :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    ((rawSectionCocone (B := C) I).w f)) x

set_option maxHeartbeats 3800000 in
/-- Rebundling an existing stage as an under-ring leaves the actual raw
representative unchanged. -/
theorem repr_stageOf {C : Type u} [CommRing C] [Algebra A C]
    [WeaklyEtale (structureMap A C)] (T : Stage A C)
    [Etale (Spec.map (U (A := A) T.carrier).hom)]
    (x : (sectionDiagram (B := C) I).obj T) :
    incl I (stageOf (U (A := A) T.carrier) T.toChart.toUnder) x = incl I T x := by
  let T₀ := stageOf (U (A := A) T.carrier) T.toChart.toUnder
  let f : T₀ ⟶ T :=
    ⟨{ toRingHom := RingHom.id T.carrier, commutes' := fun _ ↦ rfl }, by
      apply AlgHom.ext
      intro x
      rfl⟩
  have he : etaleMap f = 𝟙 (etaleObject T) := by
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_id _
  have h : (sectionDiagram (B := C) I).map f x = x := by
    change I.obj.map (etaleMap f).op x = x
    rw [he]
    simp
  exact (repr_natural I f x).symm.trans (congrArg (incl I T) h)

set_option maxHeartbeats 4800000 in
/-- A finite model carrying a glued section gives the required
preimage in the literal raw section group of the native affine base. -/
theorem exists_raw_preimage (k : B →ₐ[A] D)
    {T V M : Under (R (A := A))}
    [Etale (Spec.map T.hom)] [Etale (Spec.map V.hom)] [Etale (Spec.map M.hom)]
    (a : T ⟶ U (A := A) B) (b : V ⟶ U (A := A) D)
    (f : T ⟶ V) (v : M ⟶ V) (h : f ≫ b = a ≫ k.toUnder)
    (x : I.obj.obj (op (obj M))) (s : I.obj.obj (op (obj T)))
    (hs : I.obj.map (arrow f).op s = I.obj.map (arrow v).op x) :
    ∃ y : (raw (X (A := A)) I).obj (op (ProetaleAffineTensor.object A B)),
      (raw (X (A := A)) I).map (chartMap k).op y =
        incl I (stageOf M (v ≫ b)) x := by
  let T₀ := stageOf T a
  let V₀ := stageOf V b
  let M₀ := stageOf M (v ≫ b)
  let f₀ : stageAfterMap k T₀ ⟶ V₀ := ⟨CommRingCat.toAlgHom f, by
    change (CommRingCat.toAlgHom b).comp (CommRingCat.toAlgHom f) =
      k.comp (CommRingCat.toAlgHom a)
    rw [← CommRingCat.toAlgHom_comp, h, CommRingCat.toAlgHom_comp]
    rfl⟩
  let v₀ : M₀ ⟶ V₀ := ⟨CommRingCat.toAlgHom v, rfl⟩
  refine ⟨incl I T₀ s, ?_⟩
  have ht := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (rawSection_map I k T₀)) s
  calc
    _ = incl I (stageAfterMap k T₀) s := ht
    _ = incl I V₀ ((sectionDiagram (B := D) I).map f₀ s) := (repr_natural I f₀ s).symm
    _ = incl I V₀ ((sectionDiagram (B := D) I).map v₀ x) := congrArg (incl I V₀) hs
    _ = _ := repr_natural I v₀ x

end
end ManuscriptAudit.NativeAffineRawGluedRepresentatives

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRawGluedRepresentatives.exists_raw_preimage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
