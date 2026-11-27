import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricEuler
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleHOneNontrivial

/-! Nontrivial native pro-étale adic H¹ on the literal proper odd
geometric fibres of the same fixed integral nodal family. -/

namespace ManuscriptAudit.IntegralNodalProetaleHOneNontrivial

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField geometricFiber geometricToBase projectiveIso)
open EtaleProetaleHausdorffDirectImage (DiscreteGroup discreteEquiv adicDirectImageIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

/-- The literal geometric fibre at every odd residue prime has nontrivial
Mathlib native pro-étale ℓ-adic H¹ for every prime ℓ. -/
theorem properHOne_nontrivial (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) :
    Nontrivial ((geometricFiber p).EllAdicCohomology ℓ 1) := by
  let X := geometricFiber p
  let M := AddCommGrpCat.of (DiscreteGroup ℤ_[ℓ])
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (geometricToBase p)
  have h2 : (2 : closureField p) ≠ 0 := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)
  let e := discreteEquiv ℤ_[ℓ]
  let m : M := e.symm 1
  have hm : m ≠ 0 := by
    simpa only [m, map_zero] using e.symm.injective.ne (one_ne_zero : (1 : ℤ_[ℓ]) ≠ 0)
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj M
  let s := SchemeIsoSmallEtaleCohomology.schemeIsoCohomologyEquiv (projectiveIso p) M 1
  letI := NodalProjectiveConductorClass.projectiveHOne_nontrivial (closureField p) M h2 m hm
  letI : Nontrivial (Sheaf.H F 1) := s.symm.injective.nontrivial
  let i := adicDirectImageIso X ℓ
  have hi : Function.LeftInverse (Sheaf.H.map i.inv 1) (Sheaf.H.map i.hom 1) := by
    intro z
    rw [← Sheaf.H.map_comp_apply, i.hom_inv_id, Sheaf.H.map_id_apply]
  letI := hi.injective.nontrivial
  exact (EtaleProetaleHOneUniverseComparison.comparison_injective X (X.ellAdicSheaf ℓ)).nontrivial

end
end ManuscriptAudit.IntegralNodalProetaleHOneNontrivial

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntegralNodalProetaleHOneNontrivial.properHOne_nontrivial
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
