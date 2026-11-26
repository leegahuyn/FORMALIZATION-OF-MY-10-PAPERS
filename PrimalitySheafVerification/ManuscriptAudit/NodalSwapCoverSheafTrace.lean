import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorPresentation
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverAffineTrace

/-!
# The actual diagonal and trace on the affine étale basis of the node

The middle sheaf is the actual direct image along the crossed cover.
The tensor presentation identifies each affine value with the space
used by the affine trace. The pointwise kernel is the diagonal.
-/

namespace ManuscriptAudit.NodalSwapCoverSheafTrace

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalConductor NodalSwapCover
open AffineEtaleTensorPresentation CertifiedTorsorSpectrumTrace

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A : Type u := ↥(coordinates K)
private abbrev E : Type u := Cover K
private abbrev X := base (A K)
private abbrev cover := affineMap (A K) (E K)
private abbrev Y := Spec (CommRingCat.of (E K))
private abbrev aff := (X K).AffineEtale
private abbrev site := Scheme.AffineEtale.topology (X K)

attribute [local instance] objectAlgebra

private abbrev restriction :=
  (Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{u}).inverse

/-- Discrete continuous functions on the actual affine étale basis. -/
abbrev baseFunctions : Sheaf (site K) AddCommGrpCat.{u} :=
  (restriction K).obj (EtaleContinuousMapSheaf.continuousMapSheaf (X K) M)

/-- The actual direct image of discrete continuous functions on the crossed cover. -/
abbrev coverFunctions : Sheaf (site K) AddCommGrpCat.{u} :=
  (restriction K).obj ((SmallEtaleBaseChange.directImage (cover K) AddCommGrpCat.{u}).obj
    (EtaleContinuousMapSheaf.continuousMapSheaf (Y K) M))

private abbrev fiber (U : aff K) := pullback U.hom (cover K)
private abbrev projectionOf (U : aff K) := pullback.fst U.hom (cover K)
private abbrev fiberIso (U : aff K) := tensorIsoPullback (A K) (E K) U

private def asMap {V W : Scheme.{u}} (f : V ⟶ W) : C(V, W) := ⟨f, f.continuous⟩

private def precompose {V W : Scheme.{u}} (f : V ⟶ W) : C(W, M) →+ C(V, M) where
  toFun x := x.comp (asMap f)
  map_zero' := by ext p; rfl
  map_add' x y := by ext p; rfl

private abbrev underlying {U V : aff K} (f : U ⟶ V) :=
  ((Scheme.AffineEtale.Spec (X K)).map f).left

private abbrev fiberMap {U V : aff K} (f : U ⟶ V) :=
  ((SmallEtaleBaseChange.etaleBaseChange (cover K)).map
    ((Scheme.AffineEtale.Spec (X K)).map f)).left

private theorem fiberMap_fst {U V : aff K} (f : U ⟶ V) :
    fiberMap K f ≫ projectionOf K V = projectionOf K U ≫ underlying K f := by
  change fiberMap K f ≫
      pullback.fst ((Scheme.AffineEtale.Spec (X K)).obj V).hom (cover K) =
    pullback.fst ((Scheme.AffineEtale.Spec (X K)).obj U).hom (cover K) ≫ underlying K f
  simp only [SmallEtaleBaseChange.etaleBaseChange, MorphismProperty.Over.pullback_map_left,
    pullback.lift_fst]

set_option maxHeartbeats 1600000 in
def diagonal : baseFunctions K M ⟶ coverFunctions K M :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom (precompose M (projectionOf K U.unop))
     naturality := fun {U V} f => by
      apply ConcreteCategory.hom_ext
      intro x
      apply ContinuousMap.ext
      intro p
      change x (underlying K f.unop (projectionOf K V.unop p)) =
        x (projectionOf K U.unop (fiberMap K f.unop p))
      exact congrArg (fun k : fiber K V.unop ⟶ Spec (objectRing (A K) U.unop) => x (k p))
        (fiberMap_fst K f.unop).symm }⟩

private def traceApp (h2 : (2 : K) ≠ 0) (U : aff K) :
    C(fiber K U, M) →+ C(Spec (objectRing (A K) U), M) :=
  (NodalSwapCoverAffineTrace.affineTrace K (objectRing (A K) U) M h2).comp
    (precompose M (fiberIso K U).hom)

set_option maxHeartbeats 1700000 in
def trace (h2 : (2 : K) ≠ 0) : coverFunctions K M ⟶ baseFunctions K M :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom (traceApp K M h2 U.unop)
     naturality := fun {U V} f => by
      apply ConcreteCategory.hom_ext
      intro s
      change traceApp K M h2 V.unop (s.comp (asMap (fiberMap K f.unop))) =
        (traceApp K M h2 U.unop s).comp (asMap (underlying K f.unop))
      have hTransport :
          (s.comp (asMap (fiberMap K f.unop))).comp (asMap (fiberIso K V.unop).hom) =
            (s.comp (asMap (fiberIso K U.unop).hom)).comp
              (asMap (tensorMap (A K) (E K) f.unop)) := by
        apply ContinuousMap.ext
        intro p
        exact congrArg (fun k : tensorScheme (A K) (E K) V.unop ⟶ fiber K U.unop => s (k p))
          (tensorIsoPullback_natural (A K) (E K) f.unop).symm
      change NodalSwapCoverAffineTrace.affineTrace K (objectRing (A K) V.unop) M h2
          ((s.comp (asMap (fiberMap K f.unop))).comp (asMap (fiberIso K V.unop).hom)) = _
      rw [hTransport]
      exact NodalSwapCoverAffineTrace.affineTrace_natural K
        (R := objectRing (A K) U.unop) (S := objectRing (A K) V.unop) (M := M)
        h2 (objectAlgHom (A K) f.unop) (s.comp (asMap (fiberIso K U.unop).hom)) }⟩

private theorem precompose_fiberIso_injective (U : aff K) :
    Function.Injective (precompose M (fiberIso K U).hom) := by
  intro s t h
  apply ContinuousMap.ext
  intro p
  have hEq := congrArg
    (fun z : C(tensorScheme (A K) (E K) U, M) => z ((fiberIso K U).inv p)) h
  have hId := congrArg (fun f : fiber K U ⟶ fiber K U => f p) (fiberIso K U).inv_hom_id
  change (fiberIso K U).hom ((fiberIso K U).inv p) = p at hId
  change s ((fiberIso K U).hom ((fiberIso K U).inv p)) =
    t ((fiberIso K U).hom ((fiberIso K U).inv p)) at hEq
  simpa only [hId] using hEq

set_option maxHeartbeats 1800000 in
theorem trace_app_kernel (h2 : (2 : K) ≠ 0) (htwo : ∀ m : M, m + m = 0)
    (U : aff K) (s : (coverFunctions K M).obj.obj (op U)) :
    (trace K M h2).hom.app (op U) s = 0 ↔
    ∃ t : (baseFunctions K M).obj.obj (op U), (diagonal K M).hom.app (op U) t = s := by
  change traceApp K M h2 U s = 0 ↔
    ∃ t : C(Spec (objectRing (A K) U), M), precompose M (projectionOf K U) t = s
  change NodalSwapCoverAffineTrace.affineTrace K (objectRing (A K) U) M h2
    (precompose M (fiberIso K U).hom s) = 0 ↔ _
  rw [NodalSwapCoverAffineTrace.affineTrace_kernel K (objectRing (A K) U) M h2 htwo]
  have hComp (t : C(Spec (objectRing (A K) U), M)) :
      t.comp (projection (objectRing (A K) U)
          (NodalSwapCoverAffineTrace.coverOver K (objectRing (A K) U))) =
        precompose M (fiberIso K U).hom (precompose M (projectionOf K U) t) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg (fun k : tensorScheme (A K) (E K) U ⟶ Spec (objectRing (A K) U) => t (k p))
      (tensorIsoPullback_hom_fst (A K) (E K) U).symm
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, precompose_fiberIso_injective K M U ((hComp t).symm.trans ht)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (hComp t).trans (congrArg (precompose M (fiberIso K U).hom) ht)⟩


set_option maxHeartbeats 1800000 in
theorem trace_app_surjective_of_affine_trace_surjective (h2 : (2 : K) ≠ 0) (U : aff K)
    (hSurj : Function.Surjective
      (NodalSwapCoverAffineTrace.affineTrace K (objectRing (A K) U) M h2)) :
    Function.Surjective ((trace K M h2).hom.app (op U)) := by
  intro t
  change C(Spec (objectRing (A K) U), M) at t
  obtain ⟨s, hs⟩ := hSurj t
  refine ⟨s.comp (asMap (fiberIso K U).inv), ?_⟩
  change NodalSwapCoverAffineTrace.affineTrace K (objectRing (A K) U) M h2
    ((s.comp (asMap (fiberIso K U).inv)).comp (asMap (fiberIso K U).hom)) = t
  have hComp :
      (s.comp (asMap (fiberIso K U).inv)).comp (asMap (fiberIso K U).hom) = s := by
    apply ContinuousMap.ext
    intro p
    exact congrArg (fun f : tensorScheme (A K) (E K) U ⟶ tensorScheme (A K) (E K) U =>
      s (f p)) (fiberIso K U).hom_inv_id
  rwa [hComp]

set_option maxHeartbeats 1300000 in
theorem diagonal_app_injective (h2 : (2 : K) ≠ 0) (U : aff K) :
    Function.Injective ((diagonal K M).hom.app (op U)) := by
  intro s t h
  change precompose M (projectionOf K U) s = precompose M (projectionOf K U) t at h
  apply ContinuousMap.ext
  intro p
  have hcover : Function.Surjective (cover K) := NodalSwapCoverEtale.cover_spec_surjective K h2
  obtain ⟨q, hq⟩ := hcover (U.hom p)
  obtain ⟨x, hx, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.hom) (g := cover K) p q hq.symm
  have hst := congrArg (fun z : C(fiber K U, M) => z x) h
  change s (projectionOf K U x) = t (projectionOf K U x) at hst
  rwa [hx] at hst

end

end ManuscriptAudit.NodalSwapCoverSheafTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCoverSheafTrace.diagonal,
        ``ManuscriptAudit.NodalSwapCoverSheafTrace.trace,
        ``ManuscriptAudit.NodalSwapCoverSheafTrace.trace_app_kernel,
        ``ManuscriptAudit.NodalSwapCoverSheafTrace.trace_app_surjective_of_affine_trace_surjective,
        ``ManuscriptAudit.NodalSwapCoverSheafTrace.diagonal_app_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
