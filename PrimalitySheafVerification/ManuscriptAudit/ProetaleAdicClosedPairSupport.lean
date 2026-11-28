import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicOpenSupportCriterion
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDisjointClosedSupport

/-! For a quasi-compact open complementary to two closed supports, the
actual native adic extension by zero is the kernel of the two restrictions. -/

namespace ManuscriptAudit.ProetaleAdicClosedPairSupport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open OpenProetaleExtension (extensionByZero restriction abelianExtensionByZeroAdjunction)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X B₀ B₁ U : Scheme.{0}} (i₀ : B₀ ⟶ X) (i₁ : B₁ ⟶ X)
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev J := Scheme.ProEt.topology X

abbrev boundary : Sheaf (J (X := X)) A := functionsOver (M ℓ) i₀ ⨯ functionsOver (M ℓ) i₁

/-- The actual pair of native restrictions to the two closed supports. -/
def pairRestriction : functions (M ℓ) X ⟶ boundary i₀ i₁ ℓ :=
  prod.lift (diagonal (M ℓ) i₀) (diagonal (M ℓ) i₁)

abbrev support := kernel (pairRestriction i₀ i₁ ℓ)

abbrev inclusion : support i₀ i₁ ℓ ⟶ functions (M ℓ) X :=
  kernel.ι (pairRestriction i₀ i₁ ℓ)

private theorem first_zero : inclusion i₀ i₁ ℓ ≫ diagonal (M ℓ) i₀ = 0 := by
  rw [← show pairRestriction i₀ i₁ ℓ ≫ prod.fst = diagonal (M ℓ) i₀ from prod.lift_fst _ _,
    ← Category.assoc, kernel.condition, zero_comp]

private theorem second_zero : inclusion i₀ i₁ ℓ ≫ diagonal (M ℓ) i₁ = 0 := by
  rw [← show pairRestriction i₀ i₁ ℓ ≫ prod.snd = diagonal (M ℓ) i₁ from prod.lift_snd _ _,
    ← Category.assoc, kernel.condition, zero_comp]

private theorem section_value_zero {B : Scheme.{0}} (i : B ⟶ X)
    {F : Sheaf (J (X := X)) A} (m : F ⟶ functions (M ℓ) X)
    (hm : m ≫ diagonal (M ℓ) i = 0)
    (T : X.ProEt) (s : F.obj.obj (op T)) (x : T.left) (hx : T.hom x ∈ Set.range i) :
    (show C(T.left, M ℓ) from (m.hom.app (op T) s).down) x = 0 := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.hom) (g := i) x z hz.symm
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : F ⟶ functionsOver (M ℓ) i ↦ f.hom.app (op T)) hm) s
  have h' := congrArg
    (fun f : ULift.{1} (C(↥(pullback T.hom i : Scheme.{0}), M ℓ)) ↦ f.down p) h
  change (show C(T.left, M ℓ) from (m.hom.app (op T) s).down) (pullback.fst T.hom i p) = 0 at h'
  rwa [hp] at h'

variable [IsClosedImmersion i₀] [IsClosedImmersion i₁]
variable (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

def restrictionIso (h : Set.range j = (Set.range i₀ ∪ Set.range i₁)ᶜ) :
    (restriction j A).obj (support i₀ i₁ ℓ) ≅ functions (M ℓ) U := by
  let R := restriction j A
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  have hD₀ : Disjoint (Set.range j) (Set.range i₀) := Set.disjoint_left.mpr (by
    intro x hx h₀
    rw [h] at hx
    exact hx (Or.inl h₀))
  have hD₁ : Disjoint (Set.range j) (Set.range i₁) := Set.disjoint_left.mpr (by
    intro x hx h₁
    rw [h] at hx
    exact hx (Or.inr h₁))
  have h₀ := ProetaleDisjointClosedSupport.restriction_closed_isZero i₀ j (M ℓ) hD₀
  have h₁ := ProetaleDisjointClosedSupport.restriction_closed_isZero i₁ j (M ℓ) hD₁
  let e := PreservesLimitPair.iso R (functionsOver (M ℓ) i₀) (functionsOver (M ℓ) i₁)
  have hz : IsZero (R.obj (functionsOver (M ℓ) i₀) ⨯ R.obj (functionsOver (M ℓ) i₁)) := by
    rw [IsZero.iff_id_eq_zero]
    apply prod.hom_ext
    · exact h₀.eq_of_tgt _ _
    · exact h₁.eq_of_tgt _ _
  have hR : R.map (pairRestriction i₀ i₁ ℓ) = 0 := (hz.of_iso e).eq_of_tgt _ _
  letI := kernel.ι_of_zero hR
  exact PreservesKernel.iso R (pairRestriction i₀ i₁ ℓ) ≪≫
    asIso (kernel.ι (R.map (pairRestriction i₀ i₁ ℓ))) ≪≫ restrictionFunctionsIso j (M ℓ)

/-- The actual two-boundary support kernel is the genuine native extension of the open. -/
def extensionKernelIso (h : Set.range j = (Set.range i₀ ∪ Set.range i₁)ᶜ) :
    (extensionByZero j A).obj (functions (M ℓ) U) ≅ support i₀ i₁ ℓ := by
  have hv : ProetaleAdicOpenSupportCriterion.VanishesOutside j ℓ (inclusion i₀ i₁ ℓ) := by
    intro T s x hx
    have hm : T.hom x ∈ Set.range i₀ ∪ Set.range i₁ := by
      by_contra h'
      exact hx (h.symm ▸ h')
    rcases hm with h₀ | h₁
    · exact section_value_zero ℓ i₀ (inclusion i₀ i₁ ℓ) (first_zero i₀ i₁ ℓ) T s x h₀
    · exact section_value_zero ℓ i₁ (inclusion i₀ i₁ ℓ) (second_zero i₀ i₁ ℓ) T s x h₁
  exact ((extensionByZero j A).mapIso (restrictionIso i₀ i₁ ℓ j h)).symm ≪≫
    ProetaleAdicOpenSupportCriterion.extensionIso j ℓ (inclusion i₀ i₁ ℓ) hv

end

end ManuscriptAudit.ProetaleAdicClosedPairSupport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicClosedPairSupport.extensionKernelIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
