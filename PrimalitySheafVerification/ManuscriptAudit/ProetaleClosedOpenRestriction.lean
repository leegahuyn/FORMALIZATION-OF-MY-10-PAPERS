import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedExtensionKernel

/-! In the complementary open the actual closed direct image is zero,
and the support kernel restricts to the original continuous sheaf. -/

namespace ManuscriptAudit.ProetaleClosedOpenRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedKernelLocalSupport (K)
open ProetaleClosedExtensionKernel (extensionKernelIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z Y : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : Y ⟶ X) [IsOpenImmersion j]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

private abbrev A := AddCommGrpCat.{1}

private theorem empty_closed_pullback (U : Y.ProEt) (hComplement : Set.range j = (Set.range i)ᶜ) :
    IsEmpty (↥(pullback (U.hom ≫ j) i : Scheme.{0})) := by
  constructor
  intro x
  let a := pullback.fst (U.hom ≫ j) i x
  let b := pullback.snd (U.hom ≫ j) i x
  have h : j (U.hom a) = i b :=
    congrArg (fun f : pullback (U.hom ≫ j) i ⟶ X ↦ f x)
      (pullback.condition (f := U.hom ≫ j) (g := i))
  have hmem : j (U.hom a) ∈ Set.range j := ⟨U.hom a, rfl⟩
  rw [hComplement] at hmem
  exact hmem ⟨b, h.symm⟩

theorem restriction_closed_isZero (hComplement : Set.range j = (Set.range i)ᶜ) :
    IsZero ((restriction j A).obj (functionsOver M i)) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  letI := empty_closed_pullback i j U.unop hComplement
  apply ULift.ext
  exact ContinuousMap.ext (fun x ↦ isEmptyElim x)

/-- Actual restriction along an open is the same sheaf of continuous functions on that open. -/
def restrictionFunctionsIso :
    (restriction j A).obj (functions M X) ≅ functions M Y :=
  (sheafToPresheaf (Scheme.ProEt.topology Y) A).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro U V f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp] <;> rfl))

def restrictionKernelIso (hComplement : Set.range j = (Set.range i)ᶜ) :
    (restriction j A).obj (K i M) ≅ functions M Y := by
  let R := restriction j A
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  have h : R.map (diagonal M i) = 0 :=
    (restriction_closed_isZero i j M hComplement).eq_of_tgt _ _
  letI := kernel.ι_of_zero h
  exact PreservesKernel.iso R (diagonal M i) ≪≫ asIso (kernel.ι (R.map (diagonal M i))) ≪≫
    restrictionFunctionsIso j M

variable [DiscreteTopology M]

/-- The actual j! of discrete continuous functions is the closed restriction kernel. -/
def extensionFunctionsIsoKernel (hComplement : Set.range j = (Set.range i)ᶜ) :
    (extensionByZero j A).obj (functions M Y) ≅ K i M :=
  ((extensionByZero j A).mapIso (restrictionKernelIso i j M hComplement).symm) ≪≫
    extensionKernelIso i j M hComplement

end
end ManuscriptAudit.ProetaleClosedOpenRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleClosedOpenRestriction.restriction_closed_isZero,
      ``ManuscriptAudit.ProetaleClosedOpenRestriction.extensionFunctionsIsoKernel] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
