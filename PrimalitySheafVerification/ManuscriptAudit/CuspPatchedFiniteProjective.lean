import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspEtaleConductorPatch
import PrimalitySheafVerification.ManuscriptAudit.CuspFiniteEtaleBases
import PrimalitySheafVerification.ManuscriptAudit.CuspMilnorCoefficients

/-!
# The actual conductor-patched algebra is finite projective

Basis coordinates identify the underlying module of the actual ring
pullback with the finite projective coordinate patch. The two chosen
projections agree with their respective coordinate projections.
-/

namespace ManuscriptAudit.CuspPatchedFiniteProjective

open CategoryTheory CategoryTheory.Limits Polynomial
open CuspDelta CuspPunctured CuspEtaleCommonQuotient CuspEtaleConductorPatch
open CuspFiniteEtaleBases CuspMilnorCoefficients
open scoped Matrix TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (E : Type u) [CommRing E] [Algebra (Polynomial K) E]
variable [Algebra.Etale (Polynomial K) E] [Module.Finite (Polynomial K) E]

private abbrev A := CuspSubalgebra K
private abbrev D := cuspSquareQuotient K
private abbrev F := residueFiber K E
private abbrev L := patchRing K E

local instance normalizationResidueAlgebra : Algebra (Polynomial K) K :=
  Polynomial.constantCoeff.toAlgebra

local instance originAlgebra : Algebra (A K) K := (cuspOriginResidue K).toAlgebra

local instance normalizationTower : IsScalarTower (A K) (Polynomial K) E where
  smul_assoc a b x := by
    change ((a : Polynomial K) * b) • x = (a : Polynomial K) • (b • x)
    exact mul_smul _ _ _

local instance fiberTower : IsScalarTower (A K) K (F K E) where
  smul_assoc a k x := by
    change ((a : Polynomial K) • k) • x = (a : Polynomial K) • (k • x)
    exact smul_assoc _ _ _

local instance descendedAlgebra : Algebra (A K) (L K E) := patchAlgebra K E

private abbrev normalizationCoordinates :=
  (normalizationBasis K E).2.equivFun.restrictScalars (A K)

private abbrev residueCoordinates := (residueBasis K E).equivFun.restrictScalars (A K)

private abbrev coordinatePatch :=
  MilnorCoordinatePatch.patch (quotientMap K) (constantMap K) (transitionMatrix K E).val

/-- The first projection of the actual conductor pullback as a cusp-algebra map. -/
def firstProjection : L K E →ₐ[A K] E :=
  { (patchCone K E).fst.hom with
    commutes' := fun a => by
      change (patchCone K E).fst.hom ((cuspToPatch K E).hom a) =
        algebraMap (Polynomial K) E (algebraMap (A K) (Polynomial K) a)
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (cuspToPatch_fst K E)) a }

private def second : L K E →ₐ[A K] F K E :=
  { (patchCone K E).snd.hom with
    commutes' := fun a => by
      have h : (patchCone K E).snd.hom ((cuspToPatch K E).hom a) =
          algebraMap K (F K E) (cuspOriginResidue K a) :=
        DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (cuspToPatch_snd K E)) a
      change (patchCone K E).snd.hom ((cuspToPatch K E).hom a) =
        algebraMap (Polynomial K) (F K E) (a : Polynomial K)
      rw [h, IsScalarTower.algebraMap_apply (Polynomial K) K (F K E)] <;> rfl }

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private def coordinateMap : L K E →ₗ[A K] coordinatePatch K E :=
  let a := (normalizationCoordinates K E).toLinearMap.comp (firstProjection K E).toLinearMap
  let b := (residueCoordinates K E).toLinearMap.comp (second K E).toLinearMap
  (a.prod b).codRestrict (coordinatePatch K E) fun z => by
    rw [MilnorCoordinatePatch.mem_patch_iff]
    change (algebraMap (Polynomial K) (D K) ∘ (normalizationBasis K E).2.equivFun (firstProjection K E z)) =
      (transitionMatrix K E).val *ᵥ
        (algebraMap K (D K) ∘ (residueBasis K E).equivFun (second K E z))
    apply (conductor_coordinate_equation K E (firstProjection K E z) (second K E z)).mp
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (patch_isPullback K E).w) z

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem coordinateMap_bijective : Function.Bijective (coordinateMap K E) := by
  constructor
  · intro x y h
    have hf := congrArg (fun z : coordinatePatch K E => z.val.1) h
    have hs := congrArg (fun z : coordinatePatch K E => z.val.2) h
    change normalizationCoordinates K E (firstProjection K E x) =
      normalizationCoordinates K E (firstProjection K E y) at hf
    change residueCoordinates K E (second K E x) = residueCoordinates K E (second K E y) at hs
    have hNorm := (normalizationCoordinates K E).injective hf
    have hRes := (residueCoordinates K E).injective hs
    exact Subtype.ext (Prod.ext hNorm hRes)
  · intro x
    let a := (normalizationCoordinates K E).symm x.val.1
    let b := (residueCoordinates K E).symm x.val.2
    have hCoord := (MilnorCoordinatePatch.mem_patch_iff
      (quotientMap K) (constantMap K) (transitionMatrix K E).val x.val).mp x.property
    have hA : (normalizationBasis K E).2.equivFun a = x.val.1 :=
      (normalizationCoordinates K E).apply_symm_apply _
    have hB : (residueBasis K E).equivFun b = x.val.2 :=
      (residueCoordinates K E).apply_symm_apply _
    have hCompat : (normalizationToCommon K E).hom a = (residueToCommon K E).hom b := by
      apply (conductor_coordinate_equation K E a b).mpr
      rw [hA, hB]
      exact hCoord
    let z : L K E := ⟨(a, b), hCompat⟩
    refine ⟨z, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (normalizationBasis K E).2.equivFun a = x.val.1
      exact hA
    · change (residueBasis K E).equivFun b = x.val.2
      exact hB

/-- Actual conductor patching of finite étale algebras is the native
coordinate patch at the level of cusp modules. -/
def patchModuleEquiv : L K E ≃ₗ[A K] coordinatePatch K E :=
  LinearEquiv.ofBijective (coordinateMap K E) (coordinateMap_bijective K E)


/-- The first coordinate of the patch equivalence is the actual first projection
expressed in the normalization basis. -/
theorem patchModuleEquiv_fst (x : L K E) :
    (patchModuleEquiv K E x).val.1 =
      (normalizationBasis K E).2.equivFun (firstProjection K E x) := rfl

/-- The actual ring pullback is finite and projective as a cusp module. -/
theorem patch_finite_projective :
    Module.Finite (A K) (L K E) ∧ Module.Projective (A K) (L K E) := by
  obtain ⟨hFinite, hProjective⟩ := CuspMilnorCoefficients.finite_projective K _ (transitionMatrix K E)
  letI := hFinite
  letI := hProjective
  let e := (patchModuleEquiv K E).symm
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    Module.Projective.of_split e.symm.toLinearMap e.toLinearMap (by
      apply LinearMap.ext
      intro x
      exact e.apply_symm_apply x)⟩

end

end ManuscriptAudit.CuspPatchedFiniteProjective

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspPatchedFiniteProjective.patchModuleEquiv,
      ``ManuscriptAudit.CuspPatchedFiniteProjective.patch_finite_projective,
      ``ManuscriptAudit.CuspPatchedFiniteProjective.patchModuleEquiv_fst] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
