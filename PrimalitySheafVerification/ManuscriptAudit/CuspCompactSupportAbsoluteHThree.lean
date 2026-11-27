import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineEtaleHThree
import PrimalitySheafVerification.ManuscriptAudit.CuspCohomologyFromCharts
import PrimalitySheafVerification.ManuscriptAudit.CuspHTwoCyclic
import PrimalitySheafVerification.ManuscriptAudit.LaurentEtaleHTwo

/-! Compactly supported degree-three cohomology of the native cusp and its puncture. -/

namespace ManuscriptAudit.CuspCompactSupportAbsoluteHThree

open CategoryTheory CuspCompactSupportSequence CuspCohomologyFromCharts

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [fp : Fact p.Prime] [cp : CharP K p]
variable (d : ℕ) [NeZero (d : K)]

include p fp cp

theorem cuspHcThree_subsingleton :
    Subsingleton (cuspHc K (AddCommGrpCat.of (ZMod d)) 3) :=
  cuspHc_succ_subsingleton K p (AddCommGrpCat.of (ZMod d)) 2
    (CuspCompactSupportDegreeTwo.affineLine_cyclic_HTwo_subsingleton_of_field K d
      (RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton K))
    (AffineLineDivisorSheaf.affineLine_cyclic_HThree_subsingleton K d)
    (PrincipalOpenEtaleHTwo.laurent_cyclic_HTwo_subsingleton K d)

theorem punctureHcThree_subsingleton :
    Subsingleton (punctureHc K (AddCommGrpCat.of (ZMod d)) 3) := by
  let e := compactSupportHigherEquiv K (AddCommGrpCat.of (ZMod d)) 1
  let h := cuspHcThree_subsingleton K p d
  exact ⟨fun x y => e.injective (h.elim _ _)⟩

end
end ManuscriptAudit.CuspCompactSupportAbsoluteHThree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportAbsoluteHThree.cuspHcThree_subsingleton,
      ``ManuscriptAudit.CuspCompactSupportAbsoluteHThree.punctureHcThree_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
