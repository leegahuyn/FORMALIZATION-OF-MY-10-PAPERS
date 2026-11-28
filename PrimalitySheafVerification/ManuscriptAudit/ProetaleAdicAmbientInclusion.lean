import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenContinuousPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactHTwoAmbient

/-! The ambient map of the actual compact-support pullback is the same
inclusion used in the established single- and two-boundary computations. -/

namespace ManuscriptAudit.ProetaleAdicAmbientInclusion

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleOpenContinuousPullback (ambient)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso restrictionKernelIso)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleAdicClosedPairSupport (pairRestriction inclusion restrictionIso)
open ProetaleOpenCounitMono (extensionRestrictionMap)
open OpenProetaleExtension (restriction extensionByZero abelianExtensionByZeroAdjunction)
open ProetaleAdicCompactHTwoAmbient (singleEquiv singleEquiv_apply_val pairEquiv pairEquiv_apply_val)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private theorem restriction_comp
    {F G : P X} (g : F ⟶ G) :
    let R := restriction j A
    letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
    letI : R.Additive := R.additive_of_preserves_binary_products
    (PreservesKernel.iso R g).hom ≫ kernel.ι (R.map g) = R.map (kernel.ι g) := by
  let R := restriction j A
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  let e := PreservesKernel.iso R g
  have h : e.inv ≫ R.map (kernel.ι g) = kernel.ι (R.map g) := PreservesKernel.iso_inv_ι R g
  change e.hom ≫ kernel.ι (R.map g) = _
  rw [← h, Iso.hom_inv_id_assoc]

private theorem restriction_inv
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {F : P X} (inc : F ⟶ functions M X)
    (e : (restriction j A).obj F ≅ functions M U)
    (h : e.hom = (restriction j A).map inc ≫ (restrictionFunctionsIso j M).hom) :
    e.inv ≫ (restriction j A).map inc = (restrictionFunctionsIso j M).inv := by
  let w := restrictionFunctionsIso j M
  apply (cancel_mono w.hom).mp
  rw [Category.assoc, ← h, e.inv_hom_id, w.inv_hom_id]

private theorem counit_ambient
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {F : P X} (inc : F ⟶ functions M X)
    (e : (restriction j A).obj F ≅ functions M U)
    (h : e.inv ≫ (restriction j A).map inc = (restrictionFunctionsIso j M).inv) :
    (((extensionByZero j A).mapIso e).inv ≫ extensionRestrictionMap j F) ≫ inc =
      ambient M j := by
  let a := abelianExtensionByZeroAdjunction j
  apply (a.homEquiv (functions M U) (functions M X)).injective
  rw [a.homEquiv_naturality_right]
  change (a.homEquiv (functions M U) F) ((extensionByZero j A).map e.inv ≫ a.counit.app F) ≫
    (restriction j A).map inc = _
  rw [← a.homEquiv_counit, Equiv.apply_symm_apply]
  change e.inv ≫ (restriction j A).map inc =
    (a.homEquiv _ _) ((a.homEquiv _ _).symm (restrictionFunctionsIso j M).inv)
  rw [Equiv.apply_symm_apply, h]

variable [QuasiCompact j]
variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]

set_option maxHeartbeats 7400000 in
theorem single_ambient (i : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion i]
    (h : Set.range j = (Set.range i)ᶜ) :
    (ProetaleAdicClosedSupportKernel.extensionKernelIso i j ℓ h).hom ≫
      ProetaleClosedKernelLocalSupport.inc i ℤ_[ℓ] = ambient ℤ_[ℓ] j := by
  let g := diagonal ℤ_[ℓ] i
  let R := restriction j A
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  let e := restrictionKernelIso i j ℤ_[ℓ] h
  have he : e.hom = R.map (kernel.ι g) ≫ (restrictionFunctionsIso j ℤ_[ℓ]).hom := by
    change (PreservesKernel.iso R g).hom ≫
      (kernel.ι (R.map g) ≫ (restrictionFunctionsIso j ℤ_[ℓ]).hom) = _
    rw [← Category.assoc, restriction_comp j g]
  exact counit_ambient j ℤ_[ℓ] (kernel.ι g) e (restriction_inv j ℤ_[ℓ] (kernel.ι g) e he)

set_option maxHeartbeats 7600000 in
theorem pair_ambient (i₀ i₁ : Spec (CommRingCat.of K) ⟶ X)
    [IsClosedImmersion i₀] [IsClosedImmersion i₁]
    (h : Set.range j = (Set.range i₀ ∪ Set.range i₁)ᶜ) :
    (ProetaleAdicClosedPairSupport.extensionKernelIso i₀ i₁ ℓ j h).hom ≫ inclusion i₀ i₁ ℓ =
      ambient ℤ_[ℓ] j := by
  let g := pairRestriction i₀ i₁ ℓ
  let R := restriction j A
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  let e := restrictionIso i₀ i₁ ℓ j h
  have he : e.hom = R.map (kernel.ι g) ≫ (restrictionFunctionsIso j ℤ_[ℓ]).hom := by
    change (PreservesKernel.iso R g).hom ≫
      (kernel.ι (R.map g) ≫ (restrictionFunctionsIso j ℤ_[ℓ]).hom) = _
    rw [← Category.assoc, restriction_comp j g]
  exact counit_ambient j ℤ_[ℓ] (kernel.ι g) e (restriction_inv j ℤ_[ℓ] (kernel.ι g) e he)

private abbrev Hc := Sheaf.H ((extensionByZero j A).obj (functions ℤ_[ℓ] U)) 2

/-- Forgetting support in actual degree two is injective with one rational boundary point. -/
theorem single_injective (i : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion i]
    (h : Set.range j = (Set.range i)ᶜ) :
    Function.Injective (Sheaf.H.map (ambient ℤ_[ℓ] j) 2) := by
  let e := singleEquiv K ℓ j i h
  have hv (x : Hc j ℓ) :
      (e x).val = Sheaf.H.map (ambient ℤ_[ℓ] j) 2 x := by
    rw [singleEquiv_apply_val]
    exact (Sheaf.H.map_comp_apply
      (f := (ProetaleAdicClosedSupportKernel.extensionKernelIso i j ℓ h).hom)
      (n := 2) (ProetaleClosedKernelLocalSupport.inc i ℤ_[ℓ]) x).symm.trans
      (congrArg (fun q ↦ Sheaf.H.map q 2 x) (single_ambient j K ℓ i h))
  intro x y hxy
  apply e.injective
  exact Subtype.ext ((hv x).trans (hxy.trans (hv y).symm))

/-- Forgetting support is injective with two disjoint rational boundary points. -/
theorem pair_injective (i₀ i₁ : Spec (CommRingCat.of K) ⟶ X)
    [IsClosedImmersion i₀] [IsClosedImmersion i₁]
    (hD : Disjoint (Set.range i₀) (Set.range i₁))
    (h : Set.range j = (Set.range i₀ ∪ Set.range i₁)ᶜ) :
    Function.Injective (Sheaf.H.map (ambient ℤ_[ℓ] j) 2) := by
  let e := pairEquiv K ℓ j i₀ i₁ hD h
  have hv (x : Hc j ℓ) :
      (e x).val = Sheaf.H.map (ambient ℤ_[ℓ] j) 2 x := by
    rw [pairEquiv_apply_val]
    exact (Sheaf.H.map_comp_apply
      (f := (ProetaleAdicClosedPairSupport.extensionKernelIso i₀ i₁ ℓ j h).hom)
      (n := 2) (inclusion i₀ i₁ ℓ) x).symm.trans
      (congrArg (fun q ↦ Sheaf.H.map q 2 x) (pair_ambient j K ℓ i₀ i₁ h))
  intro x y hxy
  apply e.injective
  exact Subtype.ext ((hv x).trans (hxy.trans (hv y).symm))

end
end ManuscriptAudit.ProetaleAdicAmbientInclusion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleAdicAmbientInclusion.single_injective,
      ``ManuscriptAudit.ProetaleAdicAmbientInclusion.pair_injective] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
