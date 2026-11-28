import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicNativeExactSequence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! The actual adic residue kernel is preserved by the native coefficient
lift and its composite with a pro-étale direct image. -/

namespace ManuscriptAudit.ProetaleAdicResidueKernelMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleResidueSheaves (residueSheaf residueReduction residueTransition)
open ProetaleCoefficientUniverseLift (lift epi_map_of_chartwise)
open ComplexTowerDifference (difference map_difference_comp_comparison)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{0}

section Functor

variable {D : Type*} [Category D] [Abelian D] [HasLimitsOfShape (Discrete ℕ) D]
variable (F : A X ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesLimitsOfShape (Discrete ℕ) F]

abbrev residue (n : ℕ) := F.obj (residueSheaf X ℓ n)
abbrev step (n : ℕ) := F.map (residueTransition X ℓ n)

private abbrev δ := ProetaleAdicProductKernel.difference X ℓ
private abbrev ι := ProetaleAdicProductKernel.inclusion X ℓ

private def comparison : F.obj (ProetaleAdicProductKernel.product X ℓ) ≅ ∏ᶜ (residue X ℓ F) :=
  PreservesProduct.iso F (residueSheaf X ℓ)

/-- The actual shifted difference commutes with the product comparison. -/
theorem difference_comparison :
    F.map (δ X ℓ) ≫ (comparison X ℓ F).hom =
      (comparison X ℓ F).hom ≫ difference (residue X ℓ F) (step X ℓ F) := by
  rw [comparison, PreservesProduct.iso_hom]
  exact map_difference_comp_comparison (residueSheaf X ℓ) (residueTransition X ℓ) F

abbrev inclusion : F.obj (X.ellAdicSheaf ℓ) ⟶ ∏ᶜ (residue X ℓ F) :=
  Pi.lift (fun n ↦ F.map (residueReduction X ℓ n))

private theorem inclusion_eq :
    inclusion X ℓ F = F.map (ι X ℓ) ≫ (comparison X ℓ F).hom := by
  apply Pi.hom_ext
  intro n
  rw [Pi.lift_π, Category.assoc, comparison, PreservesProduct.iso_hom,
    piComparison_comp_π, ← F.map_comp, ProetaleAdicProductKernel.inclusion_π]

theorem inclusion_comp :
    inclusion X ℓ F ≫ difference (residue X ℓ F) (step X ℓ F) = 0 := by
  rw [inclusion_eq, Category.assoc, ← difference_comparison, ← Category.assoc,
    ← F.map_comp, ProetaleAdicProductKernel.inclusion_comp_difference, F.map_zero, zero_comp]

/-- The genuine compatible residue map remains the kernel after the
native additive, left-exact coefficient functor. -/
def inclusionIsKernel :
    IsLimit (KernelFork.ofι (inclusion X ℓ F) (inclusion_comp X ℓ F)) := by
  let e := comparison X ℓ F
  have h := isLimitForkMapOfIsLimit' F
    (ProetaleAdicProductKernel.inclusion_comp_difference X ℓ)
    (ProetaleAdicProductKernel.inclusionIsKernel X ℓ)
  have hm : Mono (F.map (ι X ℓ)) := mono_of_isLimit_fork h
  have hme : Mono (inclusion X ℓ F) := by
    rw [inclusion_eq]
    letI := hm
    infer_instance
  letI := hme
  refine KernelFork.IsLimit.ofι' _ _ (fun {W} a ha ↦ ?_)
  have hw : (a ≫ e.inv) ≫ F.map (δ X ℓ) = 0 := by
    apply (cancel_mono e.hom).mp
    have he : (a ≫ e.inv) ≫ (comparison X ℓ F).hom = a := by
      change (a ≫ e.inv) ≫ e.hom = a
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    rw [Category.assoc, difference_comparison, ← Category.assoc, he, ha, zero_comp]
  let q := h.lift (KernelFork.ofι _ hw)
  have hq : q ≫ F.map (ι X ℓ) = a ≫ e.inv :=
    h.fac (KernelFork.ofι _ hw) WalkingParallelPair.zero
  refine ⟨q, ?_⟩
  rw [inclusion_eq, ← Category.assoc, hq, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- Epimorphy of the mapped difference transfers to the actual product. -/
theorem difference_epi [Epi (F.map (δ X ℓ))] :
    Epi (difference (residue X ℓ F) (step X ℓ F)) := by
  have h : Epi ((comparison X ℓ F).hom ≫ difference (residue X ℓ F) (step X ℓ F)) := by
    rw [← difference_comparison]
    infer_instance
  exact epi_of_epi ((comparison X ℓ F).hom) _

end Functor

/-- The literal product difference in native coefficients is epic
by actual chartwise lifting through every residue transition. -/
theorem native_difference_epi :
    Epi (difference (residue X ℓ (lift X)) (step X ℓ (lift X))) := by
  letI : Epi ((lift X).map (ProetaleAdicProductKernel.difference X ℓ)) :=
    epi_map_of_chartwise X _ (fun W ↦
      ProetaleAdicProductChartEpi.evaluation_difference_epi X ℓ W.unop)
  exact difference_epi X ℓ (lift X)

end
end ManuscriptAudit.ProetaleAdicResidueKernelMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicResidueKernelMap.inclusionIsKernel,
      ``ManuscriptAudit.ProetaleAdicResidueKernelMap.native_difference_epi] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
