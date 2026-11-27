import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalNativeAdicCharacteristicTwo
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalProetaleHOneEmbedding

/-! Native integral degree-one cohomology distinguishes actual
geometric fibres of the fixed integral nodal family. -/

namespace ManuscriptAudit.IntegralNodalNativeHOneJump

open AlgebraicGeometry
open IntegralNodalGeometricFiber (geometricFiber)
open IntegralNodalProetaleHOneEmbedding (properEmbedding properEmbedding_injective)

noncomputable section

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The actual native adic H¹ is trivial at (2) and nontrivial at
every odd residue prime for each odd coefficient prime. -/
theorem proper_HOne_jump (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓ₂ : ℓ ≠ 2) :
    Subsingleton ((geometricFiber 2).EllAdicCohomology ℓ 1) ∧
      Nontrivial ((geometricFiber p).EllAdicCohomology ℓ 1) := by
  refine ⟨IntegralNodalNativeAdicCharacteristicTwo.properAtTwo_subsingleton ℓ hℓ₂, ?_⟩
  refine ⟨⟨properEmbedding p ℓ hp 0, properEmbedding p ℓ hp 1, ?_⟩⟩
  intro h
  exact zero_ne_one (properEmbedding_injective p ℓ hp h)

/-- In particular, the actual native degree-one groups at (2)
and an odd residue prime admit no additive isomorphism. -/
theorem proper_HOne_noAddEquiv (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hp : 2 < p) (hℓ₂ : ℓ ≠ 2) :
    ¬ Nonempty ((geometricFiber 2).EllAdicCohomology ℓ 1 ≃+
      (geometricFiber p).EllAdicCohomology ℓ 1) := by
  obtain ⟨hTwo, hOdd⟩ := proper_HOne_jump p ℓ hp hℓ₂
  rintro ⟨e⟩
  obtain ⟨a, b, hab⟩ := hOdd.exists_pair_ne
  exact hab (e.symm.injective (hTwo.elim _ _))

end
end ManuscriptAudit.IntegralNodalNativeHOneJump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalNativeHOneJump.proper_HOne_jump,
      ``ManuscriptAudit.IntegralNodalNativeHOneJump.proper_HOne_noAddEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
