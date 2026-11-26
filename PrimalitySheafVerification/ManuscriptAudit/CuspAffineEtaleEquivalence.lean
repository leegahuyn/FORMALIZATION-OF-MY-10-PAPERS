import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspAffineEtale
import PrimalitySheafVerification.ManuscriptAudit.CuspEtaleDescent

/-!
# Affine étale invariance of the cusp in prime characteristic

Pullback along cusp normalization is an equivalence on the native
affine étale categories. Full faithfulness follows from algebra-map
descent, and essential surjectivity follows from the Frobenius square.
-/

namespace ManuscriptAudit.CuspAffineEtale

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (p : ℕ) [pPrime : Fact p.Prime] [kCharP : CharP K p]
include p pPrime kCharP

/-- Every affine étale scheme over the normalization descends in prime characteristic. -/
theorem affinePullback_essSurj : (affinePullback K).EssSurj :=
  affinePullback_essSurj_of_descent K fun T f hf =>
    letI : Etale f := hf
    CuspEtaleDescent.affine_etale_descends K p T f

/-- Cusp normalization gives an equivalence on the actual affine étale categories. -/
theorem affinePullback_isEquivalence : (affinePullback K).IsEquivalence where
  faithful := (affinePullbackFullyFaithful K).faithful
  full := (affinePullbackFullyFaithful K).full
  essSurj := affinePullback_essSurj K p

/-- The equivalence whose forward functor is pullback along cusp normalization. -/
def affineEtaleEquivalence : (Cusp K).AffineEtale ≌ (Normalization K).AffineEtale :=
  letI := affinePullback_isEquivalence K p
  (affinePullback K).asEquivalence

end

end ManuscriptAudit.CuspAffineEtale

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspAffineEtale.affinePullback_essSurj,
      ``ManuscriptAudit.CuspAffineEtale.affinePullback_isEquivalence,
      ``ManuscriptAudit.CuspAffineEtale.affineEtaleEquivalence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
