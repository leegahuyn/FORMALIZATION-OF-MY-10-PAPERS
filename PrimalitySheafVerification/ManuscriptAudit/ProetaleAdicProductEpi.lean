import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.AbProductDifference
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicProductKernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleResidueChartSurjectivity

/-! The actual residue-product difference is epic on the pro-étale topos. -/

namespace ManuscriptAudit.ProetaleAdicProductEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleResidueSheaves (residueSheaf residueTransition)
open ProetaleAdicProductKernel (inclusion difference inclusion_comp_difference inclusionIsKernel)
open ProetaleResidueChartSurjectivity (chart_difference_surjective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev J := Scheme.ProEt.topology X
private abbrev evaluationOn (W : X.ProEt) :=
  sheafToPresheaf (J X) A ⋙ (evaluation (X.ProEt)ᵒᵖ A).obj (op W)

private theorem evaluation_difference_epi (W : X.ProEt) :
    Epi ((evaluationOn X W).map (difference X ℓ)) := by
  let E := evaluationOn X W
  let G := fun n ↦ E.obj (residueSheaf X ℓ n)
  let t := fun n ↦ E.map (residueTransition X ℓ n)
  letI : E.Additive := ⟨by intros; rfl⟩
  letI : PreservesLimit (Discrete.functor (residueSheaf X ℓ)) E := by
    dsimp only [E, evaluationOn]
    infer_instance
  let e := PreservesProduct.iso E (residueSheaf X ℓ)
  let d := ComplexTowerDifference.difference G t
  letI : Epi d := AbProductDifference.difference_epi_of_surjective G t
    (chart_difference_surjective ℓ X W)
  have h : Epi (e.hom ≫ d) := inferInstance
  have w : E.map (difference X ℓ) ≫ e.hom = e.hom ≫ d :=
    ComplexTowerDifference.map_difference_comp_comparison (residueSheaf X ℓ)
      (residueTransition X ℓ) E
  rw [← w] at h
  exact (epi_comp_iff_of_isIso _ e.hom).mp h

/-- The native residue-product difference is an epimorphism of pro-étale sheaves. -/
theorem difference_epi : Epi (difference X ℓ) := by
  let E := sheafToPresheaf (J X) A
  apply E.epi_of_epi_map
  apply (NatTrans.epi_iff_epi_app _).mpr
  intro W
  exact evaluation_difference_epi X ℓ W.unop

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
  for name in [``ManuscriptAudit.ProetaleAdicProductEpi.difference_epi,
      ``ManuscriptAudit.ProetaleAdicProductEpi.product_sequence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
