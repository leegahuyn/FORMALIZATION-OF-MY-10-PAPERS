import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedRestrictionEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedSupportKernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! Native continuous adic compact degree one for an open with a rational
closed complement and the actual closed direct image. -/

namespace ManuscriptAudit.ProetaleAdicOpenClosedHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleContinuousDirectImageGlobal (HZeroEquiv terminalEquiv finalObject)
open ProetaleClosedKernelLocalSupport (K inc)
open OpenProetaleExtension (extensionByZero)
open ProetaleAdicClosedSupportKernel (extensionKernelIso)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} (L : Type) [Field L] [IsAlgClosed L]
  (i : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev M := ℤ_[ℓ]

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev integers := (constantSheaf (J (X := X)) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private abbrev S := ProetaleAdicClosedRestrictionEpi.sequence i ℓ

theorem closedSequence_shortExact : (S i ℓ).ShortExact :=
  ProetaleAdicClosedRestrictionEpi.sequence_shortExact i ℓ

theorem restriction_HZero_surjective : Function.Surjective (Sheaf.H.map (diagonal (M ℓ) i) 0) := by
  let hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  let e := HZeroEquiv (M ℓ) i
  let u := Sheaf.H.equiv₀ (functions (M ℓ) X) hT
  intro x
  let y := e x (IsLocalRing.closedPoint L)
  refine ⟨u.symm ⟨ContinuousMap.const X y⟩, e.injective ?_⟩
  apply ContinuousMap.ext
  intro z
  change terminalEquiv (M ℓ) i ((Sheaf.H.equiv₀ (functionsOver (M ℓ) i) hT)
    (Sheaf.H.map (diagonal (M ℓ) i) 0 (u.symm ⟨ContinuousMap.const X y⟩))) z = e x z
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  change e x (IsLocalRing.closedPoint L) = e x z
  exact congrArg (e x) (Subsingleton.elim _ _)

private theorem closedImage_HOne_subsingleton : Subsingleton (Sheaf.H (functionsOver (M ℓ) i) 1) := by
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton L
    (functions (M ℓ) (Spec (CommRingCat.of L))) 0
  exact ProetaleDirectImageHOne.directImage_HOne_subsingleton i _

/-- Actual H¹ of the continuous adic support kernel maps bijectively to ambient H¹. -/
def kernelHOneEquiv : Sheaf.H (K i (M ℓ)) 1 ≃+ Sheaf.H (functions (M ℓ) X) 1 := by
  let hS := closedSequence_shortExact i ℓ
  let C := integers (X := X)
  let δ : Sheaf.H (functionsOver (M ℓ) i) 0 →+ Sheaf.H (K i (M ℓ)) 1 :=
    hS.extClass.postcomp C (show 0 + 1 = 1 by rfl)
  have he := Ext.covariant_sequence_exact₃' C hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at he
  have hE : Function.Exact (Sheaf.H.map (diagonal (M ℓ) i) 0) δ := he
  have δ_zero (a : Sheaf.H (functionsOver (M ℓ) i) 0) : δ a = 0 :=
    (hE a).mpr (restriction_HZero_surjective L i ℓ a)
  refine AddEquiv.ofBijective (Sheaf.H.map (inc i (M ℓ)) 1) ⟨?_, ?_⟩
  · intro a b hab
    apply sub_eq_zero.mp
    have hz : Sheaf.H.map (inc i (M ℓ)) 1 (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ C hS (a - b) hz rfl
    exact hc.symm.trans (δ_zero c)
  · intro a
    have hZ := closedImage_HOne_subsingleton L i ℓ
    exact Ext.covariant_sequence_exact₂ C hS a (hZ.elim _ _)

/-- Actual native extension-by-zero H¹ agrees with ordinary ambient H¹
for a single algebraically closed rational boundary point. -/
def compactHOneEquiv {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hComplement : Set.range j = (Set.range i)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (functions (M ℓ) Y)) 1 ≃+ Sheaf.H (functions (M ℓ) X) 1 :=
  (cohomologyIso (X := X) (extensionKernelIso i j ℓ hComplement) 1).trans
    (kernelHOneEquiv L i ℓ)

end
end ManuscriptAudit.ProetaleAdicOpenClosedHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicOpenClosedHOne.closedSequence_shortExact,
      ``ManuscriptAudit.ProetaleAdicOpenClosedHOne.restriction_HZero_surjective,
      ``ManuscriptAudit.ProetaleAdicOpenClosedHOne.kernelHOneEquiv,
      ``ManuscriptAudit.ProetaleAdicOpenClosedHOne.compactHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
