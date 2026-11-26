import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.Constructions
import PrimalitySheafVerification.ManuscriptAudit.CuspEtaleCommonQuotient

/-!
# The candidate descended cusp algebra

The étale normalization algebra and its origin fiber agree on the
square-zero conductor quotient. Their actual pullback in
`CommRingCat` has the canonical cusp algebra structure.
-/

namespace ManuscriptAudit.CuspEtaleConductorPatch

open CategoryTheory CategoryTheory.Limits Polynomial
open CuspDelta CuspPunctured CuspConductorSquare CuspEtaleCommonQuotient
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (E : Type u) [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E]

private abbrev D := cuspSquareQuotient K
private abbrev T := D K ⊗[Polynomial K] E
private abbrev F := residueFiber K E

/-- The normalization algebra maps to its reduction on the common quotient. -/
def normalizationToCommon : CommRingCat.of E ⟶ CommRingCat.of (T K E) :=
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : E →ₐ[Polynomial K] T K E).toRingHom

/-- Reduction to the common quotient is surjective. -/
theorem normalizationToCommon_surjective :
    Function.Surjective (normalizationToCommon K E).hom :=
  Algebra.TensorProduct.includeRight_surjective E
    (show Function.Surjective (algebraMap (Polynomial K) (D K)) from reduction_surjective K)

/-- The origin fiber maps to the common quotient by extension of constants. -/
def residueToCommon : CommRingCat.of (F K E) ⟶ CommRingCat.of (T K E) :=
  CommRingCat.ofHom <| (commonQuotientComparison K E).symm.toRingHom.comp
    (Algebra.TensorProduct.includeRight : F K E →ₐ[K] D K ⊗[K] F K E).toRingHom

/-- The chosen categorical pullback cone defining the candidate descended algebra. -/
def patchCone : PullbackCone (normalizationToCommon K E) (residueToCommon K E) :=
  CommRingCat.pullbackCone (normalizationToCommon K E) (residueToCommon K E)

/-- The ring obtained by patching the normalization algebra and its residue fiber. -/
abbrev patchRing : CommRingCat.{u} := (patchCone K E).pt

/-- The patched ring satisfies the universal property of the actual ring pullback. -/
theorem patch_isPullback :
    IsPullback (patchCone K E).fst (patchCone K E).snd
      (normalizationToCommon K E) (residueToCommon K E) :=
  IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit
    (normalizationToCommon K E) (residueToCommon K E))

private abbrev cuspToNormalization : CommRingCat.of (CuspSubalgebra K) ⟶ CommRingCat.of E :=
  CuspScheme.inclusion K ≫ CommRingCat.ofHom (algebraMap (Polynomial K) E)

private abbrev cuspToFiber : CommRingCat.of (CuspSubalgebra K) ⟶ CommRingCat.of (F K E) :=
  origin K ≫ CommRingCat.ofHom (algebraMap K (F K E))

set_option backward.isDefEq.respectTransparency false in
private theorem patchCompatibility :
    cuspToNormalization K E ≫ normalizationToCommon K E =
      cuspToFiber K E ≫ residueToCommon K E := by
  let i : E →ₐ[Polynomial K] T K E := Algebra.TensorProduct.includeRight
  let j : F K E →ₐ[K] D K ⊗[K] F K E := Algebra.TensorProduct.includeRight
  let e := commonQuotientComparison K E
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change i (algebraMap (Polynomial K) E ((CuspScheme.inclusion K).hom a)) =
    e.symm (j (algebraMap K (F K E) ((origin K).hom a)))
  rw [i.commutes, j.commutes,
    IsScalarTower.algebraMap_apply (Polynomial K) (D K) (T K E),
    IsScalarTower.algebraMap_apply K (D K) (D K ⊗[K] F K E), e.symm.commutes]
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (conductor_isPullback K).w) a
  change algebraMap (Polynomial K) (D K) ((CuspScheme.inclusion K).hom a) =
    algebraMap K (D K) ((origin K).hom a) at h
  exact congrArg (algebraMap (D K) (T K E)) h

/-- The coordinate map from the cusp ring into the patched algebra. -/
def cuspToPatch : CommRingCat.of (CuspSubalgebra K) ⟶ patchRing K E :=
  (patch_isPullback K E).lift (cuspToNormalization K E) (cuspToFiber K E)
    (patchCompatibility K E)

@[simp]
theorem cuspToPatch_fst :
    cuspToPatch K E ≫ (patchCone K E).fst = cuspToNormalization K E :=
  (patch_isPullback K E).lift_fst _ _ _

@[simp]
theorem cuspToPatch_snd :
    cuspToPatch K E ≫ (patchCone K E).snd = cuspToFiber K E :=
  (patch_isPullback K E).lift_snd _ _ _

/-- The canonical cusp algebra structure on the candidate descended ring. -/
def patchAlgebra : Algebra (CuspSubalgebra K) (patchRing K E) :=
  (cuspToPatch K E).hom.toAlgebra

end

end ManuscriptAudit.CuspEtaleConductorPatch

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspEtaleConductorPatch.patch_isPullback,
      ``ManuscriptAudit.CuspEtaleConductorPatch.normalizationToCommon_surjective,
      ``ManuscriptAudit.CuspEtaleConductorPatch.cuspToPatch_fst,
      ``ManuscriptAudit.CuspEtaleConductorPatch.cuspToPatch_snd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
