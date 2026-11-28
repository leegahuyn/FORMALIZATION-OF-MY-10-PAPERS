import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRelativeTensorPullback
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRelativeMatching
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRelativeColimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawRelativeGluing

/-! Literal singleton gluing for the raw affine étale Kan extension
on the actual native affine site. -/

namespace ManuscriptAudit.NativeAffineRawSingletonGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap specMap)
open AffineEtaleStageCategory (Stage hom)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineEtaleCoverModelIso (original)
open NativeAffineRelativeTensorPullback (relativeMap left right exists_matching_representatives)
open NativeAffineEtaleRawStageElements (chartMap)
open NativeAffineEtaleKanComparison (raw)
open AffineStageTensorExtensionMaps (extend extendMap)
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
  [WeaklyEtale (structureMap A B)] [WeaklyEtale (structureMap A D)] [WeaklyEtale (structureMap B D)]

private abbrev X := spectrum A
private abbrev d := relativeMap (A := A) (B := B) (D := D)
private abbrev f := chartMap (d (A := A) (B := B) (D := D))

variable (I : Sheaf (X (A := A)).smallEtaleTopology AddCommGrpCat.{u + 1})

private abbrev P := raw (X (A := A)) I

set_option maxHeartbeats 11000000 in
/-- The raw presheaf has actual singleton gluing on the chart,
assuming the genuine finite étale approximation of its two affine rings. -/
theorem exists_glue (hB : FiniteTupleApproximation A B) (hD : FiniteTupleApproximation A D)
    (hCover : Function.Surjective (specMap A (d (A := A) (B := B) (D := D))))
    (x : (P I).obj (op (ProetaleAffineTensor.object A D)))
    (hx : (P I).map (pullback.fst (f (A := A) (B := B) (D := D))
        (f (A := A) (B := B) (D := D))).op x =
      (P I).map (pullback.snd (f (A := A) (B := B) (D := D))
        (f (A := A) (B := B) (D := D))).op x) :
    ∃ pre : (P I).obj (op (ProetaleAffineTensor.object A B)),
      (P I).map (f (A := A) (B := B) (D := D)).op pre = x := by
  obtain ⟨M, z, N, p, q, hz, hpq⟩ := exists_matching_representatives I x hx
  have hApprox : FiniteTupleApproximation B D :=
    AffineEtaleStageRelativeColimit.relative_approximation hD
  obtain ⟨U, m, n, hm, hp, hq⟩ :=
    AffineEtaleStageRelativeMatching.exists_relative_stage hApprox M.toChart N.toChart
      (hom p) (hom q) p.property q.property
  let F := U.carrier
  letI : Algebra A F := Algebra.compHom F (algebraMap A B)
  letI : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq' rfl
  let r : F →ₐ[A] D := U.toChart.restrictScalars A
  let l : F →ₐ[A] F ⊗[B] F := (includeLeft : F →ₐ[B] _).restrictScalars A
  let h : F →ₐ[A] F ⊗[B] F := (includeRight : F →ₐ[B] _).restrictScalars A
  let v : M.carrier →ₐ[A] F := (m.restrictScalars A).comp includeRight
  let w : N.carrier →ₐ[A] F ⊗[B] F := (n.restrictScalars A).comp includeRight
  have hr : r.comp (IsScalarTower.toAlgHom A B F) = d (A := A) (B := B) (D := D) := by
    apply AlgHom.ext
    intro b
    exact U.toChart.commutes b
  have hv : r.comp v = M.toChart := by
    apply AlgHom.ext
    intro t
    have ht := DFunLike.congr_fun hm ((1 : B) ⊗ₜ[A] t)
    change r (v t) = extend (B := B) M.toChart ((1 : B) ⊗ₜ[A] t) at ht
    exact ht.trans (DFunLike.congr_fun (AffineStageTensorExtensionMaps.extend_includeRight
      (B := B) M.toChart) t)
  have hL : w.comp (hom p) = l.comp v := by
    apply AlgHom.ext
    intro t
    exact DFunLike.congr_fun hp ((1 : B) ⊗ₜ[A] t)
  have hR : w.comp (hom q) = h.comp v := by
    apply AlgHom.ext
    intro t
    exact DFunLike.congr_fun hq ((1 : B) ⊗ₜ[A] t)
  letI : Etale (Spec.map (original (A := A) M.carrier).hom) :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := (original (A := A) M.carrier).hom)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  letI : Etale (Spec.map (original (A := A) N.carrier).hom) :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := (original (A := A) N.carrier).hom)).mpr
      ((RingHom.etale_algebraMap).mpr inferInstance)
  obtain ⟨pre, hpre⟩ := NativeAffineRawRelativeGluing.exists_glue I hB
    (d (A := A) (B := B) (D := D)) r hr hCover
    ((RingHom.finitePresentation_algebraMap).mpr inferInstance)
    ((RingHom.finitePresentation_algebraMap).mpr inferInstance)
    (hom p).toUnder (hom q).toUnder v.toUnder w.toUnder
    (congrArg AlgHom.toUnder hL) (congrArg AlgHom.toUnder hR) z hpq
  rw [← AlgHom.toUnder_comp, hv, NativeAffineRawGluedRepresentatives.repr_stageOf, hz] at hpre
  exact ⟨pre, hpre⟩

end
end ManuscriptAudit.NativeAffineRawSingletonGluing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineRawSingletonGluing.exists_glue
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
