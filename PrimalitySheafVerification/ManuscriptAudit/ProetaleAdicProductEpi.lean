import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicProductChartEpi

/-! The actual residue-product difference is epic on the pro-étale topos. -/

namespace ManuscriptAudit.ProetaleAdicProductEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAdicProductKernel (inclusion difference inclusion_comp_difference inclusionIsKernel)

noncomputable section

set_option backward.defeqAttrib.useBackward true

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The native product difference is epic on every individual chart. -/
theorem evaluation_difference_epi (W : X.ProEt) :
    Epi ((difference X ℓ).hom.app (op W)) :=
  ProetaleAdicProductChartEpi.evaluation_difference_epi X ℓ W

set_option maxHeartbeats 300000 in
set_option synthInstance.maxHeartbeats 30000 in
/-- The native residue-product difference is an epimorphism of pro-étale sheaves. -/
theorem difference_epi : Epi (difference X ℓ) := by
  let E := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{0}
  letI : Epi (E.map (difference X ℓ)) := (NatTrans.epi_iff_epi_app _).mpr fun W ↦ by
    change Epi ((difference X ℓ).hom.app W)
    exact evaluation_difference_epi X ℓ W.unop
  exact E.epi_of_epi_map (difference X ℓ)

/-- The actual adic sheaf is the kernel of an epic consecutive residue-product difference. -/
theorem product_sequence :
    Nonempty (IsLimit (KernelFork.ofι (inclusion X ℓ) (inclusion_comp_difference X ℓ))) ∧
      Epi (difference X ℓ) :=
  ⟨⟨inclusionIsKernel X ℓ⟩, difference_epi X ℓ⟩

end
end ManuscriptAudit.ProetaleAdicProductEpi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicProductEpi.evaluation_difference_epi,
      ``ManuscriptAudit.ProetaleAdicProductEpi.difference_epi,
      ``ManuscriptAudit.ProetaleAdicProductEpi.product_sequence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
