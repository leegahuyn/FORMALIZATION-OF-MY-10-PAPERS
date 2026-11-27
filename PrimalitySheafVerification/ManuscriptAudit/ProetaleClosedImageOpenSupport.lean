import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenSupportedCounit

/-! The actual continuous-coefficient closed direct image is recovered by extension
by zero from any open containing the closed support. -/

namespace ManuscriptAudit.ProetaleClosedImageOpenSupport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension
open ProetaleOpenSupportedCounit (LocallySupported extensionRestrictionIso)
open ProetaleClosedSupportLocalConstants (openObject openArrow)
open ProetaleContinuousDirectImageMaps (functionsOver)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j]
variable (k : Z ⟶ X) [IsClosedImmersion k]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

private abbrev A := AddCommGrpCat.{1}

/-- A closed direct-image section restricts to zero on an open chart disjoint from its support. -/
theorem functionsOver_locallySupported (hk : Set.range k ⊆ Set.range j) :
    LocallySupported j (functionsOver M k) := by
  intro U s x
  by_cases hx : U.hom x ∈ Set.range j
  · let V := U.hom ⁻¹ᵁ j.opensRange
    refine ⟨V, hx, Or.inl ?_⟩
    rintro _ ⟨a, rfl⟩
    change U.hom a.val ∈ Set.range j
    exact a.property
  · let V := U.hom ⁻¹ᵁ
      (⟨(Set.range k)ᶜ, k.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens)
    have hxV : x ∈ V := fun h ↦ hx (hk h)
    refine ⟨V, hxV, Or.inr ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro p
    let W := openObject U V
    change ↥(pullback W.hom k : Scheme.{0}) at p
    let a := pullback.fst W.hom k p
    let b := pullback.snd W.hom k p
    have h : U.hom a.val = k b :=
      congrArg (fun f : pullback W.hom k ⟶ X ↦ f p) (pullback.condition (f := W.hom) (g := k))
    have hn : U.hom a.val ∉ Set.range k := a.property
    exact (hn ⟨b, h.symm⟩).elim

/-- The supported direct image is recovered by the actual extension-by-zero counit. -/
def closedImageExtensionIso (hk : Set.range k ⊆ Set.range j) :
    (extensionByZero j A).obj ((restriction j A).obj (functionsOver M k)) ≅ functionsOver M k :=
  extensionRestrictionIso j (functionsOver M k) (functionsOver_locallySupported j k M hk)

end
end ManuscriptAudit.ProetaleClosedImageOpenSupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleClosedImageOpenSupport.functionsOver_locallySupported,
      ``ManuscriptAudit.ProetaleClosedImageOpenSupport.closedImageExtensionIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
