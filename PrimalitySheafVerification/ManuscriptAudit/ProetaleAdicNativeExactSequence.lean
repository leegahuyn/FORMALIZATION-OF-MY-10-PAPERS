import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicProductChartEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCoefficientUniverseLift

/-! The actual residue-product difference gives a short exact sequence
in the same sheaf category used for Mathlib's native ℓ-adic cohomology. -/

namespace ManuscriptAudit.ProetaleAdicNativeExactSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAdicProductKernel (inclusion difference inclusion_comp_difference inclusionIsKernel)
open ProetaleCoefficientUniverseLift (lift epi_map_of_chartwise)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev raw :=
  ShortComplex.mk (inclusion X ℓ) (difference X ℓ) (inclusion_comp_difference X ℓ)

/-- The actual native adic sheaf, mapped into the product of its finite
residue sheaves, followed by identity minus the residue shift. -/
def sequence :
    ShortComplex (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}) :=
  (raw X ℓ).map (lift X)

/-- Its first arrow still realizes the actual kernel in the higher coefficient universe. -/
def firstIsKernel :
    IsLimit (KernelFork.ofι (sequence X ℓ).f (sequence X ℓ).zero) :=
  isLimitForkMapOfIsLimit' (lift X) (inclusion_comp_difference X ℓ) (inclusionIsKernel X ℓ)

/-- This is a literal short exact sequence of the actual native pro-étale sheaves. -/
theorem shortExact : (sequence X ℓ).ShortExact := by
  let S := sequence X ℓ
  have hm : Mono S.f := inferInstanceAs (Mono ((lift X).map (inclusion X ℓ)))
  have he : Epi S.g :=
    epi_map_of_chartwise X (difference X ℓ) (fun W ↦
      ProetaleAdicProductChartEpi.evaluation_difference_epi X ℓ W.unop)
  exact ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel (firstIsKernel X ℓ)) hm he

/-- The left cohomology term of the sequence is exactly Mathlib's native group. -/
def leftCohomologyEquiv (n : ℕ) :
    Sheaf.H (sequence X ℓ).X₁ n ≃+ X.EllAdicCohomology ℓ n :=
  AddEquiv.refl _

end
end ManuscriptAudit.ProetaleAdicNativeExactSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicNativeExactSequence.firstIsKernel,
      ``ManuscriptAudit.ProetaleAdicNativeExactSequence.shortExact,
      ``ManuscriptAudit.ProetaleAdicNativeExactSequence.leftCohomologyEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
