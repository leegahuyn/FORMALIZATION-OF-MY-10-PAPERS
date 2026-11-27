import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicOpenSupportCriterion
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedOpenRestriction

/-! Native adic extension by zero along a quasi-compact open is the
closed restriction kernel. Over each affine chart a genuine weakly
étale affine zero slice supplies the required local lifting. -/

namespace ManuscriptAudit.ProetaleAdicClosedSupportKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedKernelLocalSupport (K inc)
open OpenProetaleExtension (extensionByZero)
open ProetaleClosedOpenRestriction (restrictionKernelIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z Y : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev F := K i (M ℓ)

private theorem kernel_value_zero (U : X.ProEt) (s : (F i ℓ).obj.obj (op U))
    (x : U.left) (hx : U.hom x ∈ Set.range i) :
    (show C(U.left, M ℓ) from ((inc i (M ℓ)).hom.app (op U) s).down) x = 0 := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := i) x z hz.symm
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : F i ℓ ⟶ functionsOver (M ℓ) i ↦ f.hom.app (op U))
      (kernel.condition (diagonal (M ℓ) i))) s
  have h' := congrArg
    (fun f : ULift.{1} (C(↥(pullback U.hom i : Scheme.{0}), M ℓ)) ↦ f.down p) h
  change (show C(U.left, M ℓ) from ((inc i (M ℓ)).hom.app (op U) s).down)
    (pullback.fst U.hom i p) = 0 at h'
  rwa [hp] at h'

/-- The outgoing actual closed restriction kernel is extension by zero from
the complementary quasi-compact open, for genuine continuous adic coefficients. -/
def extensionKernelIso (hComplement : Set.range j = (Set.range i)ᶜ) :
    (extensionByZero j A).obj (functions (M ℓ) Y) ≅ F i ℓ := by
  have hVan : ProetaleAdicOpenSupportCriterion.VanishesOutside j ℓ (inc i (M ℓ)) := by
    intro T s x hx
    apply kernel_value_zero i ℓ T s x
    by_contra h
    exact hx (hComplement.symm ▸ h)
  exact ((extensionByZero j A).mapIso (restrictionKernelIso i j (M ℓ) hComplement)).symm ≪≫
    ProetaleAdicOpenSupportCriterion.extensionIso j ℓ (inc i (M ℓ)) hVan

end

end ManuscriptAudit.ProetaleAdicClosedSupportKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicClosedSupportKernel.extensionKernelIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
