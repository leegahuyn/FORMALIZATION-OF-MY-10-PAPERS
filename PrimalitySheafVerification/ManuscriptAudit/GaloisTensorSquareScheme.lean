import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import PrimalitySheafVerification.ManuscriptAudit.GaloisTensorSquare

/-!
# The Galois components of a scheme pullback

The pullback of the finite Galois field spectrum over the base field
is a disjoint union of copies of the extension spectrum. On a copy
indexed by an automorphism the first projection is the identity
and the second is the spectrum of that automorphism.
-/

namespace ManuscriptAudit.GaloisTensorSquare

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

variable (F L : Type u) [Field F] [Field L] [Algebra F L]

/-- The finite Galois cover, before imposing the finiteness and Galois hypotheses. -/
def baseMap : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F L))

private abbrev T := CommRingCat.of (L ⊗[F] L)

private def leftInclusion : CommRingCat.of L ⟶ T F L :=
  CommRingCat.ofHom (algebraMap L (L ⊗[F] L))

private def rightInclusion : CommRingCat.of L ⟶ T F L :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).toRingHom

/-- The scheme pullback is the spectrum of the tensor square. -/
def tensorSpecIsoPullback :
    Spec (T F L) ≅ pullback (baseMap F L) (baseMap F L) :=
  (pullbackSpecIso F L L).symm

variable [FiniteDimensional F L] [IsGalois F L]

private abbrev R (_σ : L ≃ₐ[F] L) := CommRingCat.of L

private def coordinateHom (σ : L ≃ₐ[F] L) : T F L ⟶ CommRingCat.of L :=
  CommRingCat.ofHom ((Pi.evalRingHom (fun _ : L ≃ₐ[F] L ↦ L) σ).comp
    (tensorProductEquiv F L).toRingHom)

/-- The Galois component associated with an automorphism. -/
def component (σ : L ≃ₐ[F] L) :
    Spec (CommRingCat.of L) ⟶ pullback (baseMap F L) (baseMap F L) :=
  Spec.map (coordinateHom F L σ) ≫ (tensorSpecIsoPullback F L).hom

/-- The first projection of the Galois component is the identity. -/
@[reassoc] theorem component_fst (σ : L ≃ₐ[F] L) :
    component F L σ ≫ pullback.fst (baseMap F L) (baseMap F L) = 𝟙 _ := by
  have hc : leftInclusion F L ≫ coordinateHom F L σ = 𝟙 (CommRingCat.of L) :=
    CommRingCat.hom_ext (RingHom.ext fun x ↦ by
      change tensorProductEquiv F L (x ⊗ₜ[F] (1 : L)) σ = x
      simp)
  have hp : (tensorSpecIsoPullback F L).hom ≫ pullback.fst (baseMap F L) (baseMap F L) =
      Spec.map (leftInclusion F L) := pullbackSpecIso_inv_fst' F L L
  rw [component, Category.assoc, hp, ← Spec.map_comp, hc, Spec.map_id]

/-- The second projection of the Galois component is the spectrum of the automorphism. -/
@[reassoc] theorem component_snd (σ : L ≃ₐ[F] L) :
    component F L σ ≫ pullback.snd (baseMap F L) (baseMap F L) =
      Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  have hc : rightInclusion F L ≫ coordinateHom F L σ = CommRingCat.ofHom σ.toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun x ↦ by
      change tensorProductEquiv F L ((1 : L) ⊗ₜ[F] x) σ = σ x
      simp)
  have hp : (tensorSpecIsoPullback F L).hom ≫ pullback.snd (baseMap F L) (baseMap F L) =
      Spec.map (rightInclusion F L) := pullbackSpecIso_inv_snd F L L
  rw [component, Category.assoc, hp, ← Spec.map_comp, hc]

private def productSpecIsoTensor :
    Spec (CommRingCat.of ((L ≃ₐ[F] L) → L)) ≅ Spec (T F L) :=
  Scheme.Spec.mapIso (tensorProductEquiv F L).toRingEquiv.toCommRingCatIso.op

/-- The actual finite disjoint coproduct is isomorphic to the pullback. -/
def sigmaIsoPullback :
    (∐ fun _ : L ≃ₐ[F] L ↦ Spec (CommRingCat.of L)) ≅
      pullback (baseMap F L) (baseMap F L) :=
  asIso (AlgebraicGeometry.sigmaSpec (R F L)) ≪≫ productSpecIsoTensor F L ≪≫ tensorSpecIsoPullback F L

/-- The coproduct inclusion is the displayed Galois component. -/
@[reassoc] theorem sigmaIsoPullback_ι (σ : L ≃ₐ[F] L) :
    Sigma.ι (fun _ : L ≃ₐ[F] L ↦ Spec (CommRingCat.of L)) σ ≫ (sigmaIsoPullback F L).hom =
      component F L σ := by
  change Sigma.ι _ σ ≫ (AlgebraicGeometry.sigmaSpec (R F L) ≫
    (productSpecIsoTensor F L).hom ≫ (tensorSpecIsoPullback F L).hom) = _
  have hP : (productSpecIsoTensor F L).hom =
      Spec.map (CommRingCat.ofHom (tensorProductEquiv F L).toRingHom) := rfl
  rw [AlgebraicGeometry.ι_sigmaSpec_assoc, ← Category.assoc, hP, ← Spec.map_comp] <;> rfl

/-- Each Galois component is an open immersion. -/
theorem component_isOpenImmersion (σ : L ≃ₐ[F] L) :
    IsOpenImmersion (component F L σ) := by
  rw [← sigmaIsoPullback_ι]
  infer_instance

/-- The Galois components jointly cover the underlying pullback scheme. -/
theorem component_jointly_surjective (x : ↑(pullback (baseMap F L) (baseMap F L))) :
    ∃ (σ : L ≃ₐ[F] L) (y : Spec (CommRingCat.of L)), component F L σ y = x := by
  let e := sigmaIsoPullback F L
  let s := e.inv x
  obtain ⟨⟨σ, y⟩, hy⟩ :=
    (AlgebraicGeometry.sigmaMk (fun _ : L ≃ₐ[F] L ↦ Spec (CommRingCat.of L))).surjective s
  refine ⟨σ, y, ?_⟩
  have hy' : Sigma.ι (fun _ : L ≃ₐ[F] L ↦ Spec (CommRingCat.of L)) σ y = s :=
    (AlgebraicGeometry.sigmaMk_mk (fun _ : L ≃ₐ[F] L ↦ Spec (CommRingCat.of L)) σ y).symm.trans hy
  calc
    _ = e.hom (Sigma.ι (fun _ : L ≃ₐ[F] L ↦ Spec (CommRingCat.of L)) σ y) := by
      rw [← sigmaIsoPullback_ι, Scheme.Hom.comp_apply]
    _ = e.hom s := congrArg e.hom hy'
    _ = x := by
      change (e.inv ≫ e.hom) x = x
      rw [e.inv_hom_id] <;> rfl

end

end ManuscriptAudit.GaloisTensorSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GaloisTensorSquare.tensorSpecIsoPullback,
      ``ManuscriptAudit.GaloisTensorSquare.component_fst,
      ``ManuscriptAudit.GaloisTensorSquare.component_snd,
      ``ManuscriptAudit.GaloisTensorSquare.sigmaIsoPullback,
      ``ManuscriptAudit.GaloisTensorSquare.sigmaIsoPullback_ι,
      ``ManuscriptAudit.GaloisTensorSquare.component_isOpenImmersion,
      ``ManuscriptAudit.GaloisTensorSquare.component_jointly_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
