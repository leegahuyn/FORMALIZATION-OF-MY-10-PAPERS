import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspReductionBaseChange
import PrimalitySheafVerification.ManuscriptAudit.MilnorIdentityGluing
import PrimalitySheafVerification.ManuscriptAudit.MilnorProjectivePatch

/-!
# Finite projective module gluing over the actual cusp conductor

The scalar compatibility locus for the conductor quotient is the
actual cusp ring. With this coefficient identification, coordinate
patching along an invertible transition matrix is finite projective.
-/

namespace ManuscriptAudit.CuspMilnorCoefficients

open CuspDelta CuspPunctured Polynomial

noncomputable section

universe u

variable (K : Type u) [Field K]

private abbrev A := CuspSubalgebra K
private abbrev B := Polynomial K
private abbrev D := cuspSquareQuotient K

local instance cuspOriginAlgebra : Algebra (A K) K :=
  (cuspOriginResidue K).toAlgebra

/-- The polynomial map to the conductor quotient as a map of cusp algebras. -/
abbrev quotientMap : B K →ₐ[A K] D K :=
  CuspReductionBaseChange.reductionAlg K

/-- The inclusion of residue-field constants into the conductor quotient. -/
def constantMap : K →ₐ[A K] D K :=
  { (cuspSquareReduction K).comp Polynomial.C with
    commutes' := fun a => by
      change cuspSquareReduction K (Polynomial.C (cuspOriginResidue K a)) =
        cuspSquareReduction K (a : Polynomial K)
      exact ((cusp_square_reduction_eq_constant_iff K _ _).2
        ⟨rfl, (cusp_mem_iff_coeff_one_zero K _).mp a.property⟩).symm }

/-- The coefficient map of the identity patch is bijective for the actual conductor square. -/
theorem pairMap_bijective :
    Function.Bijective (MilnorIdentityGluing.pairMap (quotientMap K) (constantMap K)) := by
  let e := paper2_cusp_conductor_pullback_equiv K
  have hVal (a : A K) :
      ((MilnorIdentityGluing.pairMap (quotientMap K) (constantMap K)) a).val = (e a).val := rfl
  constructor
  · intro a b h
    apply e.injective
    apply Subtype.ext
    exact (hVal a).symm.trans ((congrArg Subtype.val h).trans (hVal b))
  · intro v
    let v' : cuspConductorPullback K := ⟨v.val, v.property⟩
    let a := e.symm v'
    refine ⟨a, Subtype.ext ((hVal a).trans ?_)⟩
    exact congrArg Subtype.val (e.apply_symm_apply v')

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Identity transition coordinates give a free module over the cusp ring. -/
def identityPatchEquiv :
    MilnorCoordinatePatch.patch (quotientMap K) (constantMap K) (1 : Matrix n n (D K)) ≃ₗ[A K]
      (n → A K) := by
  have hPatch :
      MilnorCoordinatePatch.patch (quotientMap K) (constantMap K) (1 : Matrix n n (D K)) =
        MilnorIdentityGluing.identityPatch (quotientMap K) (constantMap K) n := by
    apply Submodule.ext
    intro x
    rw [MilnorCoordinatePatch.mem_patch_one_iff]
    change (quotientMap K ∘ x.1 = constantMap K ∘ x.2) ↔
      ∀ i, quotientMap K (x.1 i) = constantMap K (x.2 i)
    exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [hPatch]
  exact (MilnorIdentityGluing.identityPatchEquiv (quotientMap K) (constantMap K) n
    (pairMap_bijective K)).symm

/-- Every finite coordinate patch with the actual cusp conductor coefficients is projective. -/
theorem finite_projective (U : Matrix.GeneralLinearGroup n (D K)) :
    Module.Finite (A K) (MilnorCoordinatePatch.patch (quotientMap K) (constantMap K) U.val) ∧
      Module.Projective (A K) (MilnorCoordinatePatch.patch (quotientMap K) (constantMap K) U.val) := by
  have hSurj : Function.Surjective (quotientMap K) :=
    Ideal.Quotient.mk_surjective
  exact MilnorProjectivePatch.finite_projective_of_identity (quotientMap K) (constantMap K)
    hSurj U (identityPatchEquiv K (n ⊕ n))

end

end ManuscriptAudit.CuspMilnorCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspMilnorCoefficients.pairMap_bijective,
      ``ManuscriptAudit.CuspMilnorCoefficients.identityPatchEquiv,
      ``ManuscriptAudit.CuspMilnorCoefficients.finite_projective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
