import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspConductorSquare
import PrimalitySheafVerification.ManuscriptAudit.EtaleSplitSquareZero

/-!
# The common quotient for étale conductor patching on the cusp

The restriction of an étale algebra from the normalization to the
square-zero conductor quotient is canonically the extension to that
quotient of its fiber at the origin.
-/

namespace ManuscriptAudit.CuspEtaleCommonQuotient

open Polynomial
open ManuscriptAudit.CuspDelta ManuscriptAudit.CuspConductorSquare
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]

local instance normalizationResidueAlgebra : Algebra (Polynomial K) K :=
  Polynomial.constantCoeff.toAlgebra

local instance squareResidueAlgebra : Algebra (cuspSquareQuotient K) K :=
  (squareToResidue K).toAlgebra

local instance normalizationResidueTower :
    IsScalarTower (Polynomial K) (cuspSquareQuotient K) K :=
  IsScalarTower.of_algebraMap_eq fun f =>
    (squareToResidue_reduction K f).symm

local instance constantSectionTower : IsScalarTower K (cuspSquareQuotient K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change c = squareToResidue K (cuspSquareReduction K (Polynomial.C c))
    simp

variable (E : Type u) [CommRing E] [Algebra (Polynomial K) E]

/-- The fiber of the normalization algebra at the origin. -/
abbrev residueFiber := K ⊗[Polynomial K] E

set_option backward.isDefEq.respectTransparency false in
/-- The comparison used on the common quotient in cusp conductor patching.
It applies in particular to finite étale normalization algebras. -/
def commonQuotientComparison [Algebra.Etale (Polynomial K) E] :
    (cuspSquareQuotient K ⊗[Polynomial K] E) ≃ₐ[cuspSquareQuotient K]
      cuspSquareQuotient K ⊗[K] residueFiber K E :=
  EtaleSplitSquareZero.comparison (cuspSquareQuotient K) K (Polynomial K) E
    (squareToResidue_ker_sq K)

end

end ManuscriptAudit.CuspEtaleCommonQuotient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CuspEtaleCommonQuotient.commonQuotientComparison
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
