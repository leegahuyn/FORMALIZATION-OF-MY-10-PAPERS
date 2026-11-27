import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.AbProductDifference
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicProductKernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleResidueChartSurjectivity

/-! The actual residue-product difference is epic on each pro-étale chart. -/

namespace ManuscriptAudit.ProetaleAdicProductChartEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleResidueSheaves (residueSheaf residueTransition)
open ProetaleAdicProductKernel (difference)
open ProetaleResidueChartSurjectivity (chart_difference_surjective)

noncomputable section

set_option backward.defeqAttrib.useBackward true

private abbrev A := AddCommGrpCat.{0}

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

set_option maxHeartbeats 450000 in
set_option synthInstance.maxHeartbeats 30000 in
/-- The native sheaf product difference induces an epimorphism on every individual chart. -/
theorem evaluation_difference_epi (W : X.ProEt) :
    Epi ((difference X ℓ).hom.app (op W)) := by
  let J := Scheme.ProEt.topology X
  let E₁ : Sheaf J A ⥤ (X.ProEt)ᵒᵖ ⥤ A := sheafToPresheaf J A
  let E₂ : ((X.ProEt)ᵒᵖ ⥤ A) ⥤ A := (evaluation (X.ProEt)ᵒᵖ A).obj (op W)
  let E := E₁ ⋙ E₂
  change Epi (E.map (difference X ℓ))
  letI : PreservesLimitsOfShape (Discrete ℕ) E₁ := inferInstance
  letI : PreservesLimitsOfShape (Discrete ℕ) E₂ := inferInstance
  letI : PreservesLimitsOfShape (Discrete ℕ) E := comp_preservesLimitsOfShape E₁ E₂
  letI : E.Additive := ⟨by intros; rfl⟩
  let G : ℕ → A := fun n ↦ E.obj (residueSheaf X ℓ n)
  let t (n : ℕ) : G (n + 1) ⟶ G n := E.map (residueTransition X ℓ n)
  let e : E.obj (∏ᶜ residueSheaf X ℓ) ≅ ∏ᶜ G := PreservesProduct.iso E (residueSheaf X ℓ)
  let d := ComplexTowerDifference.difference G t
  letI : Epi d := AbProductDifference.difference_epi_of_surjective G t
    (chart_difference_surjective ℓ X W)
  letI : Epi (e.hom ≫ d) := epi_comp e.hom d
  have w : E.map (difference X ℓ) ≫ e.hom = e.hom ≫ d :=
    ComplexTowerDifference.map_difference_comp_comparison (residueSheaf X ℓ)
      (residueTransition X ℓ) E
  have h : Epi (E.map (difference X ℓ) ≫ e.hom) := w.symm ▸
    (inferInstanceAs (Epi (e.hom ≫ d)))
  exact (epi_comp_iff_of_isIso (E.map (difference X ℓ)) e.hom).mp h

end
end ManuscriptAudit.ProetaleAdicProductChartEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicProductChartEpi.evaluation_difference_epi
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
