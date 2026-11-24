import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured

/-!
# The cusp normalization sequence under flat base change

Over the cusp coordinate ring, the polynomial normalization
has quotient supported at the origin. Tensoring the actual inclusion and
residue map by a flat cusp algebra preserves the kernel description.
-/

namespace ManuscriptAudit.CuspFlatNormalization

open CuspDelta TensorProduct

noncomputable section

variable (K : Type*) [Field K]

private abbrev A := CuspPunctured.CuspSubalgebra K
private abbrev B := Polynomial K

/-- The actual linear map from the polynomial normalization to the residue
module at the cusp. -/
def normalizationResidue :
    B K →ₗ[A K] (A K ⧸ RingHom.ker (cuspOriginResidue K)) :=
  (paper2_cusp_quotient_residue_linear_equiv K).toLinearMap.comp (cuspInclusionSubmodule K).mkQ

/-- The elements with zero normalization residue are precisely the elements
of the cusp coordinate ring. -/
theorem normalization_exact :
    Function.Exact (Algebra.linearMap (A K) (B K)) (normalizationResidue K) := by
  intro f
  change (paper2_cusp_quotient_residue_linear_equiv K) ((cuspInclusionSubmodule K).mkQ f) = 0 ↔
    f ∈ Set.range (Algebra.linearMap (A K) (B K))
  rw [← map_zero (paper2_cusp_quotient_residue_linear_equiv K),
    (paper2_cusp_quotient_residue_linear_equiv K).injective.eq_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change f ∈ CuspPunctured.CuspSubalgebra K ↔ ∃ a : A K, (a : B K) = f
  exact ⟨fun h => ⟨⟨f, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.property⟩

variable (T : Type*) [CommRing T] [Algebra (A K) T] [Module.Flat (A K) T]

private abbrev includeBase :=
  (Algebra.TensorProduct.includeLeft : T →ₐ[A K] T ⊗[A K] B K)

private theorem unitTensor_eq_includeBase (z : T ⊗[A K] A K) :
    (Algebra.linearMap (A K) (B K)).lTensor T z =
      includeBase K T (TensorProduct.rid (A K) T z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro t a
    rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, TensorProduct.rid_tmul,
      Algebra.TensorProduct.includeLeft_apply, smul_tmul, Algebra.algebraMap_eq_smul_one]
  · intro x y hx hy
    rw [map_add, hx, hy, map_add, map_add]

/-- A flat cusp algebra injects into its actual base change to the normalization. -/
theorem includeBase_injective :
    Function.Injective (includeBase K T) :=
  Algebra.TensorProduct.includeLeft_injective Subtype.val_injective

/-- Tensoring a linear map whose kernel is the cusp preserves the
description of that kernel, with the original base algebra as its image. -/
theorem flat_exact_from_inclusion {M : Type*} [AddCommGroup M] [Module (A K) M]
    (g : B K →ₗ[A K] M) (hg : Function.Exact (Algebra.linearMap (A K) (B K)) g) :
    Function.Exact (includeBase K T).toLinearMap (g.lTensor T) := by
  have h := Module.Flat.lTensor_exact T hg
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := (h z).mp hz
    exact ⟨TensorProduct.rid (A K) T a, (unitTensor_eq_includeBase K T a).symm.trans ha⟩
  · rintro ⟨t, rfl⟩
    apply (h _).mpr
    refine ⟨t ⊗ₜ[A K] (1 : A K), ?_⟩
    rw [unitTensor_eq_includeBase, TensorProduct.rid_tmul, one_smul]

/-- After flat base change, an element of the normalization comes from the
cusp algebra precisely when its actual residue obstruction vanishes. -/
theorem flat_normalization_exact :
    Function.Exact (includeBase K T).toLinearMap ((normalizationResidue K).lTensor T) :=
  flat_exact_from_inclusion K T _ (normalization_exact K)

end

end ManuscriptAudit.CuspFlatNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspFlatNormalization.normalization_exact,
      ``ManuscriptAudit.CuspFlatNormalization.includeBase_injective,
      ``ManuscriptAudit.CuspFlatNormalization.flat_exact_from_inclusion,
      ``ManuscriptAudit.CuspFlatNormalization.flat_normalization_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
