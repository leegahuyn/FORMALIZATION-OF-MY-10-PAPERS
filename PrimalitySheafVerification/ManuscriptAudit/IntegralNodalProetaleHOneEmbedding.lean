import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalProetaleHOneNontrivial
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveConductorAdditive

/-! The actual nodal conductor injects the additive p-adic integers
into native pro-étale H¹ of the proper model and of its literal odd fibers. -/

namespace ManuscriptAudit.IntegralNodalProetaleHOneEmbedding

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber (closureField geometricFiber geometricToBase projectiveIso)
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveConductorAdditive (conductorMap conductorMap_injective)
open EtaleProetaleHausdorffDirectImage (DiscreteGroup discreteEquiv adicDirectImageIso)
open NodalProetaleHOneNontrivial (conductorComparison conductorComparison_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev M (ℓ : ℕ) [Fact ℓ.Prime] := AddCommGrpCat.of (DiscreteGroup ℤ_[ℓ])

/-- The conductor label gives an actual native pro-étale adic class on the proper split node. -/
def modelEmbedding (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (h2 : (2 : K) ≠ 0) :
    ℤ_[ℓ] →+ (projectiveNode K).EllAdicCohomology ℓ 1 :=
  (conductorComparison K ℓ).comp
    ((conductorMap K (M ℓ) h2).comp (discreteEquiv ℤ_[ℓ]).symm.toAddMonoidHom)

theorem modelEmbedding_injective (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (h2 : (2 : K) ≠ 0) :
    Function.Injective (modelEmbedding K ℓ h2) := by
  intro a b hab
  apply (discreteEquiv ℤ_[ℓ]).symm.injective
  apply conductorMap_injective K (M ℓ) h2
  apply conductorComparison_injective K ℓ
  exact hab

private theorem residueTwoNonzero (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (2 : closureField p) ≠ 0 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)

/-- The additive conductor class on a literal geometric fibre of the fixed
integral nodal family, in Mathlib's actual native pro-étale adic group. -/
def properEmbedding (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) :
    ℤ_[ℓ] →+ (geometricFiber p).EllAdicCohomology ℓ 1 :=
  let X := geometricFiber p
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (geometricToBase p)
  let s := SchemeIsoSmallEtaleCohomology.schemeIsoCohomologyEquiv (projectiveIso p) (M ℓ) 1
  let i := adicDirectImageIso X ℓ
  let c := EtaleProetaleHOneUniverseComparison.comparison X (X.ellAdicSheaf ℓ)
  c.comp ((Sheaf.H.map i.hom 1).comp (s.symm.toAddMonoidHom.comp
    ((conductorMap (closureField p) (M ℓ) (residueTwoNonzero p hp)).comp
      (discreteEquiv ℤ_[ℓ]).symm.toAddMonoidHom)))

/-- The actual proper geometric fibre at every odd residue prime contains
an additive copy of ℤℓ in native degree-one pro-étale cohomology. -/
theorem properEmbedding_injective (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) :
    Function.Injective (properEmbedding p ℓ hp) := by
  let X := geometricFiber p
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (geometricToBase p)
  let s := SchemeIsoSmallEtaleCohomology.schemeIsoCohomologyEquiv (projectiveIso p) (M ℓ) 1
  let i := adicDirectImageIso X ℓ
  have hi : Function.LeftInverse (Sheaf.H.map i.inv 1) (Sheaf.H.map i.hom 1) := by
    intro z
    rw [← Sheaf.H.map_comp_apply, i.hom_inv_id, Sheaf.H.map_id_apply]
  intro a b hab
  apply (discreteEquiv ℤ_[ℓ]).symm.injective
  apply conductorMap_injective (closureField p) (M ℓ) (residueTwoNonzero p hp)
  apply s.symm.injective
  apply hi.injective
  apply EtaleProetaleHOneUniverseComparison.comparison_injective X (X.ellAdicSheaf ℓ)
  exact hab

end
end ManuscriptAudit.IntegralNodalProetaleHOneEmbedding

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalProetaleHOneEmbedding.modelEmbedding_injective,
      ``ManuscriptAudit.IntegralNodalProetaleHOneEmbedding.properEmbedding_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
