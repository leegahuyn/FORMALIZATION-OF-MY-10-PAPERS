import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Flat
import PrimalitySheafVerification.ManuscriptAudit.CuspEtaleCommonQuotient

/-!
# Free coordinates for finite étale cusp conductor patching

The normalization polynomial ring is a PID. A finite étale algebra is
flat and hence torsion-free there, so it has a finite free basis. The
origin fiber uses the same index set by tensoring the basis. These
bases put the actual common-quotient comparison into an invertible matrix.
-/

namespace ManuscriptAudit.CuspFiniteEtaleBases

open Polynomial
open CuspDelta CuspEtaleCommonQuotient
open scoped Matrix TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (E : Type u) [CommRing E] [Algebra (Polynomial K) E]

local instance normalizationResidueAlgebra : Algebra (Polynomial K) K :=
  Polynomial.constantCoeff.toAlgebra

variable [Algebra.Etale (Polynomial K) E] [Module.Finite (Polynomial K) E]

/-- A finite free basis of the actual normalization algebra over K[t]. -/
def normalizationBasis : Σ n : ℕ, Basis (Fin n) (Polynomial K) E := by
  letI : Module.Flat (Polynomial K) E := inferInstance
  letI : Module.IsTorsionFree (Polynomial K) E := inferInstance
  exact Module.basisOfFiniteTypeTorsionFree' (R := Polynomial K) (M := E)

/-- The actual origin fiber is free on the same finite index set. -/
def residueBasis :
    Basis (Fin (normalizationBasis K E).1) K (residueFiber K E) :=
  (normalizationBasis K E).2.baseChange K

theorem normalization_and_residue_finrank :
    Module.finrank (Polynomial K) E = Module.finrank K (residueFiber K E) := by
  calc
    _ = Fintype.card (Fin (normalizationBasis K E).1) :=
      Module.finrank_eq_card_basis (normalizationBasis K E).2
    _ = _ := (Module.finrank_eq_card_basis (residueBasis K E)).symm

private def quotientNormalizationBasis :
    Basis (Fin (normalizationBasis K E).1) (cuspSquareQuotient K)
      (cuspSquareQuotient K ⊗[Polynomial K] E) :=
  (normalizationBasis K E).2.baseChange (cuspSquareQuotient K)

private def quotientResidueBasis :
    Basis (Fin (normalizationBasis K E).1) (cuspSquareQuotient K)
      (cuspSquareQuotient K ⊗[K] residueFiber K E) :=
  (residueBasis K E).baseChange (cuspSquareQuotient K)

private abbrev I := Fin (normalizationBasis K E).1
private abbrev D := cuspSquareQuotient K

private def transitionEquiv : (I K E → D K) ≃ₗ[D K] (I K E → D K) :=
  ((quotientResidueBasis K E).equivFun.symm.trans
    (commonQuotientComparison K E).symm.toLinearEquiv).trans
    (quotientNormalizationBasis K E).equivFun

/-- The transition from residue basis coordinates to normalization basis
coordinates is an actual invertible matrix over the conductor quotient. -/
def transitionMatrix : Matrix.GL (I K E) (D K) where
  val := LinearMap.toMatrix' (transitionEquiv K E).toLinearMap
  inv := LinearMap.toMatrix' (transitionEquiv K E).symm.toLinearMap
  val_inv := by
    have h : (transitionEquiv K E).toLinearMap.comp (transitionEquiv K E).symm.toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact (transitionEquiv K E).apply_symm_apply v
    rw [← LinearMap.toMatrix'_comp, h, LinearMap.toMatrix'_id]
  inv_val := by
    have h : (transitionEquiv K E).symm.toLinearMap.comp (transitionEquiv K E).toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact (transitionEquiv K E).symm_apply_apply v
    rw [← LinearMap.toMatrix'_comp, h, LinearMap.toMatrix'_id]

/-- Matrix multiplication realizes the inverse comparison on the genuine
common quotient in the two scalar-extended bases. -/
theorem transitionMatrix_mulVec (v : I K E → D K) :
    (transitionMatrix K E).val *ᵥ v =
      (quotientNormalizationBasis K E).equivFun
        ((commonQuotientComparison K E).symm ((quotientResidueBasis K E).equivFun.symm v)) :=
  LinearMap.toMatrix'_mulVec (transitionEquiv K E).toLinearMap v

end

end ManuscriptAudit.CuspFiniteEtaleBases

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspFiniteEtaleBases.normalization_and_residue_finrank,
      ``ManuscriptAudit.CuspFiniteEtaleBases.transitionMatrix,
      ``ManuscriptAudit.CuspFiniteEtaleBases.transitionMatrix_mulVec] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
