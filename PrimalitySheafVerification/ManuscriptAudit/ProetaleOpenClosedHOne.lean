import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedRestrictionEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantRestriction

/-! Native compact-support degree one for an open with single rational
closed complement, using the actual extension by zero and closed direct image. -/

namespace ManuscriptAudit.ProetaleOpenClosedHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleContinuousDirectImageGlobal (HZeroEquiv terminalEquiv finalObject)
open ProetaleClosedKernelLocalSupport (K inc)
open OpenProetaleExtension (extensionByZero)
open ProetaleClosedOpenRestriction (extensionFunctionsIsoKernel)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} (L : Type) [Field L] [IsAlgClosed L]
  (i : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev integers := (constantSheaf (J (X := X)) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private abbrev S := ShortComplex.mk (inc i M) (diagonal M i) (kernel.condition (diagonal M i))

theorem closedSequence_shortExact : (S L i M).ShortExact := by
  letI := ProetaleClosedRestrictionEpi.restriction_epi i M
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel (S L i M) (kernelIsKernel (diagonal M i)))
    inferInstance inferInstance

theorem restriction_HZero_surjective : Function.Surjective (Sheaf.H.map (diagonal M i) 0) := by
  let hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  let e := HZeroEquiv M i
  let u := Sheaf.H.equiv₀ (functions M X) hT
  intro x
  let y := e x (IsLocalRing.closedPoint L)
  refine ⟨u.symm ⟨ContinuousMap.const X y⟩, e.injective ?_⟩
  apply ContinuousMap.ext
  intro z
  change terminalEquiv M i ((Sheaf.H.equiv₀ (functionsOver M i) hT)
    (Sheaf.H.map (diagonal M i) 0 (u.symm ⟨ContinuousMap.const X y⟩))) z = e x z
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  change e x (IsLocalRing.closedPoint L) = e x z
  exact congrArg (e x) (Subsingleton.elim _ _)

private theorem closedImage_HOne_subsingleton : Subsingleton (Sheaf.H (functionsOver M i) 1) := by
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton L
    (functions M (Spec (CommRingCat.of L))) 0
  exact ProetaleDirectImageHOne.directImage_HOne_subsingleton i _

/-- Actual H¹ of the discrete support kernel maps bijectively to ambient H¹. -/
def kernelHOneEquiv : Sheaf.H (K i M) 1 ≃+ Sheaf.H (functions M X) 1 := by
  let hS := closedSequence_shortExact L i M
  let C := integers (X := X)
  let δ : Sheaf.H (functionsOver M i) 0 →+ Sheaf.H (K i M) 1 :=
    hS.extClass.postcomp C (show 0 + 1 = 1 by rfl)
  have he := Ext.covariant_sequence_exact₃' C hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at he
  have hE : Function.Exact (Sheaf.H.map (diagonal M i) 0) δ := he
  have δ_zero (a : Sheaf.H (functionsOver M i) 0) : δ a = 0 :=
    (hE a).mpr (restriction_HZero_surjective L i M a)
  refine AddEquiv.ofBijective (Sheaf.H.map (inc i M) 1) ⟨?_, ?_⟩
  · intro a b hab
    apply sub_eq_zero.mp
    have hz : Sheaf.H.map (inc i M) 1 (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ C hS (a - b) hz rfl
    exact hc.symm.trans (δ_zero c)
  · intro a
    have hZ := closedImage_HOne_subsingleton L i M
    exact Ext.covariant_sequence_exact₂ C hS a (hZ.elim _ _)

/-- Actual native extension-by-zero H¹ agrees with ordinary ambient H¹
for a single algebraically closed rational boundary point. -/
def compactHOneEquiv {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j]
    (hComplement : Set.range j = (Set.range i)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (functions M Y)) 1 ≃+ Sheaf.H (functions M X) 1 :=
  (cohomologyIso (X := X) (extensionFunctionsIsoKernel i j M hComplement) 1).trans
    (kernelHOneEquiv L i M)

/-- The same native comparison with the actual constant sheaves of a discrete group. -/
def compactConstantHOneEquiv {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j]
    (hComplement : Set.range j = (Set.range i)ᶜ) :
    Sheaf.H ((extensionByZero j A).obj (ProetaleConstantRestriction.constant Y M)) 1 ≃+
      Sheaf.H (ProetaleConstantRestriction.constant X M) 1 :=
  (cohomologyIso (X := X) ((extensionByZero j A).mapIso (ProetaleDiscreteConstant.constantIso Y M)) 1).trans
    ((compactHOneEquiv L i M j hComplement).trans
      (cohomologyIso (X := X) (ProetaleDiscreteConstant.constantIso X M) 1).symm)

end
end ManuscriptAudit.ProetaleOpenClosedHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenClosedHOne.closedSequence_shortExact,
      ``ManuscriptAudit.ProetaleOpenClosedHOne.restriction_HZero_surjective,
      ``ManuscriptAudit.ProetaleOpenClosedHOne.kernelHOneEquiv,
      ``ManuscriptAudit.ProetaleOpenClosedHOne.compactHOneEquiv,
      ``ManuscriptAudit.ProetaleOpenClosedHOne.compactConstantHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
