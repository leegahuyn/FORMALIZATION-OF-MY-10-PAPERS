import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Laurent
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenEtaleHTwo
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! Ordinary degree-two cyclic étale cohomology of the actual multiplicative line. -/

namespace ManuscriptAudit.PrincipalOpenEtaleHTwo

open AlgebraicGeometry CategoryTheory

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

/-- The native full-site H² of the Laurent spectrum with invertible
cyclic coefficients vanishes. -/
theorem laurent_cyclic_HTwo_subsingleton (K : Type) [Field K] [IsAlgClosed K]
    (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf
      (Spec (CommRingCat.of (LaurentPolynomial K))).smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ZMod d))) 2) := by
  let a : Polynomial K := Polynomial.X
  let α : Localization.Away a ≃ₐ[Polynomial K] LaurentPolynomial K :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) (LaurentPolynomial K)
  let e : Spec (CommRingCat.of (LaurentPolynomial K)) ≅ Spec (CommRingCat.of (Localization.Away a)) :=
    Scheme.Spec.mapIso α.toRingEquiv.toCommRingCatIso.op
  let h := cyclic_HTwo_subsingleton K a Polynomial.X_ne_zero d
  let eH := SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
    e (AddCommGrpCat.of (ZMod d)) 2
  exact ⟨fun x y ↦ eH.injective (h.elim _ _)⟩

end

end ManuscriptAudit.PrincipalOpenEtaleHTwo

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PrincipalOpenEtaleHTwo.laurent_cyclic_HTwo_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
