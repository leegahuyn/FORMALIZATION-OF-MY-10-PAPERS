import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveConductorClass
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveCyclicRestriction

/-! Exact geometric ordinary and compact-support degree one of the actual
split node for each invertible prime coefficient. -/

namespace ManuscriptAudit.NodalProjectivePrimeHOne

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open GeometricSkyscraperCohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private theorem surjective_of_injective {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [AddGroup G]
    (f : G →+ ZMod ℓ) (h : Function.Injective f) (hG : Nontrivial G) :
    Function.Surjective f := by
  obtain ⟨x, y, hxy⟩ := hG.exists_pair_ne
  let z := x - y
  have hz : f z ≠ 0 := by
    intro e
    apply hxy
    apply h
    exact sub_eq_zero.mp (by simpa only [z, map_sub] using e)
  intro a
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (n := ℓ) (a / f z)
  refine ⟨m • z, ?_⟩
  rw [map_zsmul, zsmul_eq_mul, hm, div_mul_cancel₀ _ hz]

variable (K : Type) [Field K] [IsAlgClosed K]

local instance (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev Ab := AddCommGrpCat.{0}
private abbrev coeff (ℓ : ℕ) := AddCommGrpCat.of (ZMod ℓ)
private abbrev properHOne (ℓ : ℕ) :=
  Sheaf.H ((constantSheaf (projectiveNode K).smallEtaleTopology Ab).obj (coeff ℓ)) 1

/-- For each invertible prime order ℓ, the actual proper split node has
exactly a single copy of ZMod ℓ in ordinary small étale H¹. -/
def projectiveHOneEquiv (h2 : (2 : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    properHOne K ℓ ≃+ ZMod ℓ := by
  let e := NodalConductorAbelianHOne.affineCyclicHOneEquiv K h2 ℓ
  let r := NodalProjectiveCyclicRestriction.restriction K ℓ
  let f : properHOne K ℓ →+ ZMod ℓ := e.symm.toAddMonoidHom.comp r
  have hi : Function.Injective f :=
    e.symm.injective.comp (NodalProjectiveCyclicRestriction.restriction_injective K ℓ)
  have h := NodalProjectiveConductorClass.projectiveHOne_nontrivial K (coeff ℓ) h2 1 one_ne_zero
  exact AddEquiv.ofBijective f ⟨hi, surjective_of_injective f hi h⟩

/-- With these same prime coefficients, the actual affine-node compactly
supported H¹ is also the cyclic group. -/
def compactHOneEquiv (h2 : (2 : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    NodalCompactSupportHOne.nodalHc K (coeff ℓ) 1 ≃+ ZMod ℓ :=
  (NodalCompactSupportHOne.nodalHcOneProjectiveEquiv K (coeff ℓ)).trans
    (projectiveHOneEquiv K h2 ℓ)

end

end ManuscriptAudit.NodalProjectivePrimeHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectivePrimeHOne.projectiveHOneEquiv,
      ``ManuscriptAudit.NodalProjectivePrimeHOne.compactHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
