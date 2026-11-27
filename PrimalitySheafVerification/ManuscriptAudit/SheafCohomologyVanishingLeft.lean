import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections

/-! Vanishing for the left term of an actual short exact sequence of étale sheaves. -/

namespace ManuscriptAudit.SheafCohomologyVanishingLeft

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe u

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

theorem H_succ_subsingleton {X : Scheme.{u}}
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (hS : S.ShortExact)
    (n : ℕ) (hRight : Subsingleton (Sheaf.H S.X₃ n))
    (hMid : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  apply subsingleton_of_forall_eq 0
  intro a
  change Ext Z S.X₁ (n + 1) at a
  have h : a.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := hMid.elim _ _
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ Z hS a h (show n + 1 = n + 1 by rfl)
  have hzero : b = 0 := hRight.elim _ _
  change a = 0
  rw [← hb, hzero, Ext.zero_comp]

end
end ManuscriptAudit.SheafCohomologyVanishingLeft

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafCohomologyVanishingLeft.H_succ_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
