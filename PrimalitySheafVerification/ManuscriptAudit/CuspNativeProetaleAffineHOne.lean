import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification
import PrimalitySheafVerification.ManuscriptAudit.CuspScheme
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUniversalHomeomorphismHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineLineAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction

/-! Native finite-cyclic and integral adic H¹ vanish on the actual
affine cusp by its verified universal homeomorphic normalization. -/

namespace ManuscriptAudit.CuspNativeProetaleAffineHOne

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (affineCusp)
open CuspScheme
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleDiscreteConstant (constantIso)
open ProetaleConstantRestriction (constant)
open ProetaleUniversalHomeomorphismHOne (HOneMap_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev L := Spec (CommRingCat.of (Polynomial K))

local instance cyclicTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance cyclicDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

theorem cyclic_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H (constant (affineCusp K) (ZMod d)) 1) := by
  letI := paper2_cusp_map_finite K
  letI := paper2_cusp_map_universally_injective K
  letI := paper2_cusp_map_surjective K
  let e := cohomologyIso (X := L K) (constantIso (L K) (ZMod d)) 1
  have h := ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton K d
  letI : Subsingleton (Sheaf.H (functions (ZMod d) (L K)) 1) := e.symm.injective.subsingleton
  have hA : Subsingleton (Sheaf.H (functions (ZMod d) (affineCusp K)) 1) :=
    (HOneMap_injective (cuspMap K) (ZMod d)).subsingleton
  let f := cohomologyIso (X := affineCusp K) (constantIso (affineCusp K) (ZMod d)) 1
  exact ⟨fun a b ↦ f.injective (hA.elim _ _)⟩

theorem adic_HOne_subsingleton (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)] :
    Subsingleton ((affineCusp K).EllAdicCohomology ℓ 1) := by
  letI := paper2_cusp_map_finite K
  letI := paper2_cusp_map_universally_injective K
  letI := paper2_cusp_map_surjective K
  let h := ProetaleAffineLineAdicHOne.adic_HOne_subsingleton K ℓ
  letI : Subsingleton (Sheaf.H (functions ℤ_[ℓ] (L K)) 1) := h
  exact (HOneMap_injective (cuspMap K) ℤ_[ℓ]).subsingleton

end
end ManuscriptAudit.CuspNativeProetaleAffineHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeProetaleAffineHOne.cyclic_HOne_subsingleton,
      ``ManuscriptAudit.CuspNativeProetaleAffineHOne.adic_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
