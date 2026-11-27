import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ComplexTowerDifference
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicResidueLimit

/-! The actual pro-étale adic sheaf is the kernel of the actual residue product difference. -/

namespace ManuscriptAudit.ProetaleAdicProductKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleResidueSheaves (residueSheaf residueTransition residueReduction residueReduction_comp)
open ProetaleAdicResidueLimit (lift lift_comp residue_hom_ext)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The categorical product of the actual residue sheaves on the same native pro-étale site. -/
abbrev product := ∏ᶜ (residueSheaf X ℓ)

/-- The actual map of the native p-adic sheaf into the product of its residues. -/
def inclusion : X.ellAdicSheaf ℓ ⟶ product X ℓ :=
  Pi.lift (residueReduction X ℓ)

@[reassoc]
theorem inclusion_π (n : ℕ) : inclusion X ℓ ≫ Pi.π (residueSheaf X ℓ) n = residueReduction X ℓ n :=
  Pi.lift_π _ _

/-- Identity minus the consecutive residue shift, on the actual sheaf product. -/
def difference : product X ℓ ⟶ product X ℓ :=
  ComplexTowerDifference.difference (residueSheaf X ℓ) (residueTransition X ℓ)

@[reassoc]
theorem difference_π (n : ℕ) : difference X ℓ ≫ Pi.π (residueSheaf X ℓ) n =
    Pi.π (residueSheaf X ℓ) n -
      Pi.π (residueSheaf X ℓ) (n + 1) ≫ residueTransition X ℓ n :=
  ComplexTowerDifference.difference_π _ _ _

theorem inclusion_comp_difference : inclusion X ℓ ≫ difference X ℓ = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, difference_π, Preadditive.comp_sub, inclusion_π,
    inclusion_π_assoc, residueReduction_comp, sub_self, zero_comp]

instance inclusion_mono : Mono (inclusion X ℓ) := by
  constructor
  intro F a b h
  apply residue_hom_ext X ℓ F
  intro n
  have h' := congrArg (fun g ↦ g ≫ Pi.π (residueSheaf X ℓ) n) h
  simpa only [Category.assoc, inclusion_π] using h'

/-- The actual compatible residue inclusion realizes the categorical kernel of the product difference. -/
def inclusionIsKernel : IsLimit (KernelFork.ofι (inclusion X ℓ) (inclusion_comp_difference X ℓ)) := by
  refine KernelFork.IsLimit.ofι' _ _ (fun {F} a ha ↦ ?_)
  let ρ (n : ℕ) := a ≫ Pi.π (residueSheaf X ℓ) n
  have hρ (n : ℕ) : ρ (n + 1) ≫ residueTransition X ℓ n = ρ n := by
    have h := congrArg (fun g ↦ g ≫ Pi.π (residueSheaf X ℓ) n) ha
    have he : ρ n - ρ (n + 1) ≫ residueTransition X ℓ n = 0 := by
      simpa only [ρ, Category.assoc, difference_π, Preadditive.comp_sub, zero_comp] using h
    exact (sub_eq_zero.mp he).symm
  refine ⟨lift X ℓ F ρ hρ, ?_⟩
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, inclusion_π, ρ] using lift_comp X ℓ F ρ hρ n

end
end ManuscriptAudit.ProetaleAdicProductKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicProductKernel.inclusion_comp_difference,
      ``ManuscriptAudit.ProetaleAdicProductKernel.inclusion_mono,
      ``ManuscriptAudit.ProetaleAdicProductKernel.inclusionIsKernel] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
