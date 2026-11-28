import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCoverSurjectiveMatching
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawGluedRepresentatives

/-! A raw section with an actual finite cover model and a literal
matching witness glues over the original native affine chart. -/

namespace ManuscriptAudit.NativeAffineRawSingletonModelGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap)
open AffineEtaleStageCategory (Stage hom)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineEtaleStageRefinementColimit (refinementDiagram refinementCocone)
open AffineStageFixedCoproductGeometry (left overlapLeft overlapRight isPullback_overlap etale_cover)
open AffineStageRefinementMatching (coverCocone)
open NativeEtaleUnderRingGluing (obj arrow)
open NativeAffineRawGluedRepresentatives (stageOf)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements (chartMap)
open NativeAffineEtaleKanComparison (raw)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A D)]

private abbrev U (C : Type u) [CommRing C] [Algebra A C] := CommRingCat.mkUnder (CommRingCat.of A) C
private abbrev X := spectrum A

variable (T : Stage A B) (E : Type u) [CommRing E]
  [Algebra T.carrier E] [Algebra.Etale T.carrier E]

private abbrev R := CommRingCat.of T.carrier
private abbrev k := CommRingCat.ofHom (algebraMap A T.carrier)
private abbrev C := refinementCocone T
private abbrev F := refinementDiagram T
private abbrev Q := CommRingCat.mkUnder (R T) E
private abbrev L := Under.map (k T)
private abbrev Mdl := coverCocone (k T) (C T) (Q T E)

private theorem baseEtale (j : Under T) :
    Etale (Spec.map ((L T).obj ((F T).obj j)).hom) := by
  have he : ((L T).obj ((F T).obj j)).hom =
      CommRingCat.ofHom (algebraMap A j.right.carrier) := by
    apply CommRingCat.hom_ext
    ext a
    exact (hom j.hom).commutes a
  rw [he]
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap A j.right.carrier))).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)

variable (I : Sheaf (X (A := A)).smallEtaleTopology AddCommGrpCat.{u + 1})

set_option maxHeartbeats 8500000 in
/-- Genuine finite model gluing produces a native raw preimage. -/
theorem exists_glue_of_model (hApprox : FiniteTupleApproximation A B) (d : B →ₐ[A] D)
    (s : (L T).obj (C T).pt ⟶ U (A := A) B) (g : (Mdl T E).pt ⟶ U (A := A) D)
    (hCover : Function.Surjective (Spec.map (left (C T).pt (Q T E)).right))
    (hg : (L T).map (left (C T).pt (Q T E)) ≫ g = s ≫ d.toUnder)
    {M N : Under (CommRingCat.of A)} [Etale (Spec.map M.hom)] [Etale (Spec.map N.hom)]
    (hM : M.hom.hom.FinitePresentation) (hN : N.hom.hom.FinitePresentation)
    (a b : M ⟶ N) (x : M ⟶ (Mdl T E).pt)
    (y : N ⟶ (coverCocone (k T) (C T) (Q T E ⨿ Q T E)).pt)
    (h₁ : a ≫ y = x ≫ (L T).map (overlapLeft (C T).pt (Q T E)))
    (h₂ : b ≫ y = x ≫ (L T).map (overlapRight (C T).pt (Q T E)))
    (z : I.obj.obj (op (obj M))) (hz : I.obj.map (arrow a).op z = I.obj.map (arrow b).op z) :
    ∃ v : (raw (X (A := A)) I).obj (op (ProetaleAffineTensor.object A B)),
      (raw (X (A := A)) I).map (chartMap d).op v =
        (rawSectionCocone (B := D) I).ι.app (stageOf M (x ≫ g)) z := by
  obtain ⟨j, v, w, hJ, hv, _, hp, hq⟩ :=
    AffineEtaleCoverSurjectiveMatching.exists_surjective_match T E hApprox hCover
      M N hM hN a b x y h₁ h₂
  let V := (F T).obj j
  let f := (L T).map (left V (Q T E))
  let p := (L T).map (overlapLeft V (Q T E))
  let q := (L T).map (overlapRight V (Q T E))
  letI : Etale (Spec.map ((L T).obj V).hom) := baseEtale T j
  have hE : Etale (Spec.map (Q T E).hom) := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale) (φ := (Q T E).hom)).mpr
    change (algebraMap T.carrier E).Etale
    exact RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale T.carrier E))
  letI : Etale (Spec.map f.right) := etale_cover V (Q T E) hE
  letI : Etale (Spec.map ((L T).obj (V ⨿ Q T E)).hom) := by
    rw [← Under.w f, Spec.map_comp]
    infer_instance
  have hPB : IsPullback (Spec.map p.right) (Spec.map q.right) (Spec.map f.right)
      (Spec.map f.right) := isPullback_overlap V (Q T E)
  letI : Etale (Spec.map p.right) := MorphismProperty.of_isPullback (P := @Etale) hPB.flip inferInstance
  letI : Etale (Spec.map ((L T).obj (V ⨿ (Q T E ⨿ Q T E))).hom) := by
    rw [← Under.w p, Spec.map_comp]
    infer_instance
  obtain ⟨t, ht⟩ := NativeEtaleUnderRingGluing.exists_glue I f p q a b v w hp hq hPB hJ z hz
  let ai : (L T).obj V ⟶ U (A := A) B := (L T).map ((C T).ι.app j) ≫ s
  let gi : (L T).obj (V ⨿ Q T E) ⟶ U (A := A) D := (Mdl T E).ι.app j ≫ g
  have hc : f ≫ (Mdl T E).ι.app j =
      (L T).map ((C T).ι.app j) ≫ (L T).map (left (C T).pt (Q T E)) := by
    change (L T).map (left V (Q T E)) ≫ (L T).map (coprod.map ((C T).ι.app j) (𝟙 _)) =
      (L T).map ((C T).ι.app j) ≫ (L T).map (left (C T).pt (Q T E))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (L T).map (coprod.inl_map ((C T).ι.app j) (𝟙 _))
  have he : f ≫ gi = ai ≫ d.toUnder := by
    change f ≫ (Mdl T E).ι.app j ≫ g = ((L T).map ((C T).ι.app j) ≫ s) ≫ d.toUnder
    rw [← Category.assoc, hc, Category.assoc, hg, Category.assoc]
  obtain ⟨r, hr⟩ := NativeAffineRawGluedRepresentatives.exists_raw_preimage I d
    (T := (L T).obj V) (V := (L T).obj (V ⨿ Q T E)) (M := M) ai gi f v he z t ht
  have hvg : v ≫ gi = x ≫ g := by
    change v ≫ (Mdl T E).ι.app j ≫ g = x ≫ g
    rw [← Category.assoc, hv]
  rw [hvg] at hr
  exact ⟨r, hr⟩

end
end ManuscriptAudit.NativeAffineRawSingletonModelGluing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRawSingletonModelGluing.exists_glue_of_model
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
