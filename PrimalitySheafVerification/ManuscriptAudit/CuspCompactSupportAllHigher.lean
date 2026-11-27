import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineEtaleAcyclic
import PrimalitySheafVerification.ManuscriptAudit.CuspCohomologyFromCharts
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportHigherComparison
import PrimalitySheafVerification.ManuscriptAudit.LaurentEtaleHigher

/-! Every compactly supported group in degree at least three vanishes on both actual curves. -/

namespace ManuscriptAudit.CuspCompactSupportAllHigher

open CategoryTheory CuspCompactSupportSequence CuspCohomologyFromCharts

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [kClosed : IsAlgClosed K]
variable (p : ℕ) [pPrime : Fact p.Prime] [pChar : CharP K p]
variable (d : ℕ) [dNZ : NeZero (d : K)]

include kClosed p pPrime pChar dNZ

theorem cuspHc_add_three_subsingleton (n : ℕ) :
    Subsingleton (cuspHc K (AddCommGrpCat.of (ZMod d)) (n + 3)) :=
  cuspHc_succ_subsingleton K p (AddCommGrpCat.of (ZMod d)) (n + 2)
    (AffineLineEtaleAcyclic.cyclic_H_succ_subsingleton K d (n + 1))
    (AffineLineEtaleAcyclic.cyclic_H_succ_subsingleton K d (n + 2))
    (LaurentEtaleHigher.cyclic_H_add_two_subsingleton K d n)

theorem punctureHc_add_three_subsingleton (n : ℕ) :
    Subsingleton (punctureHc K (AddCommGrpCat.of (ZMod d)) (n + 3)) := by
  let e := compactSupportHigherEquiv K (AddCommGrpCat.of (ZMod d)) (n + 1)
  let h := cuspHc_add_three_subsingleton K p d n
  exact ⟨fun a b => e.injective (h.elim _ _)⟩

end
end ManuscriptAudit.CuspCompactSupportAllHigher

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportAllHigher.cuspHc_add_three_subsingleton,
      ``ManuscriptAudit.CuspCompactSupportAllHigher.punctureHc_add_three_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
