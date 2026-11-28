import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictedUnits

/-! Actual restriction of the monomorphism into an injective sheaf and its
cokernel exact sequence on the affine small étale basis. -/

namespace ManuscriptAudit.AffineEtaleRestrictedResolution

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AffineEtaleOpenRestriction AffineEtaleRestrictedUnits KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev R := affineRestriction j
private abbrev G := coordinateUnitSheaf

local instance : PreservesFiniteLimits (R j) := (affineRestriction_exact j).1
local instance : PreservesFiniteColimits (R j) := (affineRestriction_exact j).2
local instance : (R j).Additive := (R j).additive_of_preserves_binary_products
local instance : (R j).PreservesInjectiveObjects := affineRestriction_preservesInjectiveObjects j

variable {I : Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{0}}
variable (i : G X ⟶ I)

/-- The original unit sheaf injection restricted to the open. -/
def restrictedInjection : G U ⟶ (R j).obj I :=
  (restrictionUnitsIso j).inv ≫ (R j).map i

instance [Mono i] : Mono (restrictedInjection j i) := by
  unfold restrictedInjection
  infer_instance

/-- Restriction takes an injective target to an injective target. -/
theorem restrictedTarget_injective [Injective I] : Injective ((R j).obj I) :=
  (R j).injective_obj I

/-- Actual cokernel comparison for the restricted map. -/
def restrictedCokernelIso :
    (R j).obj (cokernel i) ≅ cokernel (restrictedInjection j i) :=
  PreservesCokernel.iso (R j) i ≪≫
    cokernel.mapIso _ _ (restrictionUnitsIso j) (Iso.refl _) (by simp [restrictedInjection])

/-- The comparison on local sections respects the cokernel projection. -/
theorem restrictedCokernel_projection :
    (R j).map (cokernel.π i) ≫ (restrictedCokernelIso j i).hom =
      cokernel.π (restrictedInjection j i) := by
  simp [restrictedCokernelIso, cokernel.mapIso]

private abbrev embeddingSequence {C : Type*} [Category* C] [Abelian C]
    {A B : C} (f : A ⟶ B) : ShortComplex C :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

/-- The actual morphism of short exact unit embedding sequences. -/
def restrictedSequenceComparison :
    (embeddingSequence i).map (R j) ⟶ embeddingSequence (restrictedInjection j i) where
  τ₁ := (restrictionUnitsIso j).hom
  τ₂ := 𝟙 _
  τ₃ := (restrictedCokernelIso j i).hom
  comm₁₂ := by simp [restrictedInjection]
  comm₂₃ := by
    rw [Category.id_comp]
    exact (restrictedCokernel_projection j i).symm

end

end ManuscriptAudit.AffineEtaleRestrictedResolution

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleRestrictedResolution.restrictedTarget_injective,
      ``ManuscriptAudit.AffineEtaleRestrictedResolution.restrictedCokernel_projection,
      ``ManuscriptAudit.AffineEtaleRestrictedResolution.restrictedSequenceComparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
