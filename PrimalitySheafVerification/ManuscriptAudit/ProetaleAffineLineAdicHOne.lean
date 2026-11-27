import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineLineCyclicHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant

/-! Finite residue detection gives vanishing of the actual native
integral adic H¹ of affine line in invertible characteristic. -/

namespace ManuscriptAudit.ProetaleAffineLineAdicHOne

open AlgebraicGeometry CategoryTheory
open ProetaleAdicHOneDetection ProetaleDiscreteConstant
open ProetaleAffineTensor (spectrum)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := spectrum (Polynomial K)

theorem finiteResidue_HOne_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (X K) ℓ n) 1) := by
  letI : NeZero ((ℓ ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩
  let e := ProetaleCohomologyIso.cohomologyIso (X := X K) (nativeResidueIso (X K) ℓ n) 1
  have h := ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton K (ℓ ^ n)
  exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩

/-- The actual Mathlib pro-étale adic H¹ of the affine line is zero. -/
theorem adic_HOne_subsingleton : Subsingleton ((X K).EllAdicCohomology ℓ 1) := by
  constructor
  intro a b
  apply reductionMap_injective (X K) ℓ
  apply Subtype.ext
  funext n
  exact (finiteResidue_HOne_subsingleton K ℓ n).elim _ _

end
end ManuscriptAudit.ProetaleAffineLineAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineLineAdicHOne.finiteResidue_HOne_subsingleton,
      ``ManuscriptAudit.ProetaleAffineLineAdicHOne.adic_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
