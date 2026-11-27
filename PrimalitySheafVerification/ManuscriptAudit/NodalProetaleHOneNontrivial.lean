import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleHOneUniverseComparison
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleHausdorffDirectImage
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveConductorClass

/-! The conductor class on the actual proper node detects nonzero
native pro-étale ℓ-adic H¹ for every prime coefficient. -/

namespace ManuscriptAudit.NodalProetaleHOneNontrivial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase projectiveNode_isProper)
open EtaleProetaleHausdorffDirectImage (DiscreteGroup discreteEquiv adicDirectImageIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev M := AddCommGrpCat.of (DiscreteGroup ℤ_[ℓ])

private abbrev F :=
  (constantSheaf (projectiveNode K).smallEtaleTopology AddCommGrpCat.{0}).obj (M ℓ)

private theorem node_locallyNoetherian : IsLocallyNoetherian (projectiveNode K) := by
  letI : IsProper (projectiveNodeToBase K) := projectiveNode_isProper K
  exact LocallyOfFiniteType.isLocallyNoetherian (projectiveNodeToBase K)

/-- The actual étale conductor cohomology maps to native pro-étale
adic cohomology of the fixed proper nodal model. -/
def conductorComparison :
    Sheaf.H (F K ℓ) 1 →+ (projectiveNode K).EllAdicCohomology ℓ 1 :=
  letI := node_locallyNoetherian K
  let e := adicDirectImageIso (projectiveNode K) ℓ
  (EtaleProetaleHOneUniverseComparison.comparison (projectiveNode K)
    ((projectiveNode K).ellAdicSheaf ℓ)).comp (Sheaf.H.map e.hom 1)

theorem conductorComparison_injective : Function.Injective (conductorComparison K ℓ) := by
  letI := node_locallyNoetherian K
  let e := adicDirectImageIso (projectiveNode K) ℓ
  have h : Function.LeftInverse (Sheaf.H.map e.inv 1) (Sheaf.H.map e.hom 1) := by
    intro z
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  intro x y hxy
  apply h.injective
  apply EtaleProetaleHOneUniverseComparison.comparison_injective (projectiveNode K)
    ((projectiveNode K).ellAdicSheaf ℓ)
  exact hxy

/-- The actual proper split node has nontrivial Mathlib pro-étale
adic H¹ for every prime ℓ. -/
theorem properHOne_nontrivial (h2 : (2 : K) ≠ 0) :
    Nontrivial ((projectiveNode K).EllAdicCohomology ℓ 1) := by
  let e := discreteEquiv ℤ_[ℓ]
  let m : M ℓ := e.symm 1
  have hm : m ≠ 0 := by
    simpa only [m, map_zero] using e.symm.injective.ne (one_ne_zero : (1 : ℤ_[ℓ]) ≠ 0)
  letI : Nontrivial (Sheaf.H (F K ℓ) 1) :=
    NodalProjectiveConductorClass.projectiveHOne_nontrivial K (M ℓ) h2 m hm
  exact (conductorComparison_injective K ℓ).nontrivial

end
end ManuscriptAudit.NodalProetaleHOneNontrivial

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProetaleHOneNontrivial.conductorComparison_injective,
      ``ManuscriptAudit.NodalProetaleHOneNontrivial.properHOne_nontrivial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
