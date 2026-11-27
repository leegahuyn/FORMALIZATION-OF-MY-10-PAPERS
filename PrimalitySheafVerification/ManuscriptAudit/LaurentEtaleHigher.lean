import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Laurent
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenEtaleAcyclic
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! All higher constant cyclic groups on the actual multiplicative line. -/

namespace ManuscriptAudit.LaurentEtaleHigher

open AlgebraicGeometry CategoryTheory

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

theorem cyclic_H_add_two_subsingleton (K : Type) [Field K] [IsAlgClosed K]
    (d : ℕ) [NeZero (d : K)] (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf
      (Spec (CommRingCat.of (LaurentPolynomial K))).smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ZMod d))) (n + 2)) := by
  let a : Polynomial K := Polynomial.X
  let α : Localization.Away a ≃ₐ[Polynomial K] LaurentPolynomial K :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) (LaurentPolynomial K)
  let e : Spec (CommRingCat.of (LaurentPolynomial K)) ≅ Spec (CommRingCat.of (Localization.Away a)) :=
    Scheme.Spec.mapIso (CategoryTheory.Iso.op (CommRingCat.isoMk α.toRingEquiv))
  let h := PrincipalOpenEtaleAcyclic.cyclic_H_add_two_subsingleton K a Polynomial.X_ne_zero d n
  let eH := SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
    e (AddCommGrpCat.of (ZMod d)) (n + 2)
  exact ⟨fun x y => eH.injective (h.elim _ _)⟩

end
end ManuscriptAudit.LaurentEtaleHigher

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.LaurentEtaleHigher.cyclic_H_add_two_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
