import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawSingletonModelGluing
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCoverModelOverlap
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRelativeDescent

/-! A finite étale relative cover with matching data can be modeled over
an absolute étale stage, and then genuinely glued on the native chart. -/

namespace ManuscriptAudit.NativeAffineRawRelativeGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap specMap)
open AffineEtaleStageCategory (Stage)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineEtaleCoverModelIso (original baseArrow baseLimit fixedRing coverLimit baseIso coverIso coverIso_leg)
open AffineStageFixedCoproductGeometry (left overlapLeft overlapRight)
open NativeEtaleUnderRingGluing (obj arrow)
open NativeAffineRawGluedRepresentatives (stageOf)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements (chartMap)
open NativeAffineEtaleKanComparison (raw)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D F : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [CommRing D] [CommRing F]
  [Algebra A B] [Algebra A D] [Algebra A F] [Algebra B F] [IsScalarTower A B F]
  [Algebra.Etale B F]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A D)]

private abbrev X := spectrum A
private abbrev L := AffineEtaleCoverModelOverlap.inl (A := A) (B := B) (F := F)
private abbrev H := AffineEtaleCoverModelOverlap.inr (A := A) (B := B) (F := F)

variable (I : Sheaf (X (A := A)).smallEtaleTopology AddCommGrpCat.{u + 1})

set_option maxHeartbeats 9200000 in
/-- The finite relative witness produces a raw preimage along the
actual cover morphism using a genuine surjective finite cover stage. -/
theorem exists_glue (hApprox : FiniteTupleApproximation A B) (d : B →ₐ[A] D)
    (r : F →ₐ[A] D) (hr : r.comp (IsScalarTower.toAlgHom A B F) = d)
    (hSurj : Function.Surjective (specMap A d))
    {M N : Under (CommRingCat.of A)} [Etale (Spec.map M.hom)] [Etale (Spec.map N.hom)]
    (hM : M.hom.hom.FinitePresentation) (hN : N.hom.hom.FinitePresentation)
    (a b : M ⟶ N) (v : M ⟶ original (A := A) F)
    (w : N ⟶ original (A := A) (F ⊗[B] F))
    (h₁ : a ≫ w = v ≫ (L (A := A) (B := B) (F := F)).toUnder)
    (h₂ : b ≫ w = v ≫ (H (A := A) (B := B) (F := F)).toUnder)
    (z : I.obj.obj (op (obj M))) (hz : I.obj.map (arrow a).op z = I.obj.map (arrow b).op z) :
    ∃ pre : (raw (X (A := A)) I).obj (op (ProetaleAffineTensor.object A B)),
      (raw (X (A := A)) I).map (chartMap d).op pre =
        (rawSectionCocone (B := D) I).ι.app (stageOf M (v ≫ r.toUnder)) z := by
  obtain ⟨Q, hQR, hQA, hQE, q, E, hER, hEA, hEE, ⟨e⟩⟩ :=
    AffineEtaleStageRelativeDescent.exists_model (D := F) hApprox
  letI : CommRing Q := hQR
  letI : Algebra A Q := hQA
  letI : Algebra.Etale A Q := hQE
  letI : CommRing E := hER
  letI : Algebra Q E := hEA
  letI : Algebra.Etale Q E := hEE
  let T := Stage.of A B q
  letI : Algebra T.carrier E := hEA
  letI : Algebra.Etale T.carrier E := hEE
  let j := baseIso T
  let i := coverIso T E e
  let U := baseLimit T
  let V := fixedRing T E
  let K := Under.map (baseArrow T)
  let f : CommRingCat.mkUnder (CommRingCat.of A) B ⟶
      CommRingCat.mkUnder (CommRingCat.of A) F := (IsScalarTower.toAlgHom A B F).toUnder
  let f₀ := K.map (left U V)
  let p₀ := K.map (overlapLeft U V)
  let q₀ := K.map (overlapRight U V)
  have hLeg : f₀ ≫ i.hom = j.hom ≫ f := coverIso_leg T E e
  have hRing : (left U V).right ≫ i.hom.right = f.right := by
    have h := congrArg (Under.forget (CommRingCat.of A)).map hLeg
    change (left U V).right ≫ i.hom.right = 𝟙 (CommRingCat.of B) ≫ f.right at h
    simpa only [Category.id_comp] using h
  have hCover : Function.Surjective (Spec.map (left U V).right) := by
    have h : Spec.map r.toUnder.right ≫ Spec.map i.hom.right ≫ Spec.map (left U V).right =
        specMap A d := by
      rw [← Spec.map_comp, hRing, ← Spec.map_comp]
      exact congrArg (fun k : B →ₐ[A] D ↦ specMap A k) hr
    intro b₀
    obtain ⟨d₀, hd₀⟩ := hSurj b₀
    refine ⟨Spec.map i.hom.right (Spec.map r.toUnder.right d₀), ?_⟩
    change (Spec.map r.toUnder.right ≫ Spec.map i.hom.right ≫ Spec.map (left U V).right) d₀ = b₀
    rw [h]
    exact hd₀
  have hO : f₀ ≫ p₀ = f₀ ≫ q₀ := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg K.map (AffineStageFixedCoproductSquare.isPushout U V).w
  obtain ⟨m, hm₁, hm₂⟩ :=
    AffineEtaleCoverModelOverlap.exists_tensor_overlap_map j i hLeg hO
  let x := v ≫ i.inv
  let y := w ≫ m
  let g := i.hom ≫ r.toUnder
  have hg : f₀ ≫ g = j.hom ≫ d.toUnder := by
    rw [← Category.assoc, hLeg, Category.assoc]
    have hrd : f ≫ r.toUnder = d.toUnder := by
      change (IsScalarTower.toAlgHom A B F).toUnder ≫ r.toUnder = d.toUnder
      rw [← AlgHom.toUnder_comp, hr]
    rw [hrd]
  have hL : a ≫ y = x ≫ p₀ := by
    change a ≫ w ≫ m = (v ≫ i.inv) ≫ p₀
    rw [← Category.assoc, h₁, Category.assoc, hm₁, Category.assoc]
  have hR : b ≫ y = x ≫ q₀ := by
    change b ≫ w ≫ m = (v ≫ i.inv) ≫ q₀
    rw [← Category.assoc, h₂, Category.assoc, hm₂, Category.assoc]
  obtain ⟨pre, hPre⟩ := NativeAffineRawSingletonModelGluing.exists_glue_of_model T E I
    hApprox d j.hom g hCover hg hM hN a b x y hL hR z hz
  have hComp : x ≫ g = v ≫ r.toUnder := by
    change (v ≫ i.inv) ≫ i.hom ≫ r.toUnder = v ≫ r.toUnder
    rw [Category.assoc, i.inv_hom_id_assoc]
  rw [hComp] at hPre
  exact ⟨pre, hPre⟩

end
end ManuscriptAudit.NativeAffineRawRelativeGluing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRawRelativeGluing.exists_glue
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
