import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import PrimalitySheafVerification.ManuscriptAudit.EtaleFieldChartExactSections
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleHOneDetection
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleSkyscraperResolution
import PrimalitySheafVerification.ManuscriptAudit.GaloisSectionSequence
import PrimalitySheafVerification.ManuscriptAudit.GaloisSkyscraperSectionCohomology
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyPositiveShift

/-!
# Higher étale vanishing from acyclic finite Galois section representations

Take an injective skyscraper presentation. Evaluation is exact on
étale field charts by degree-one detection. The middle Galois section
representation is acyclic, so the quotient retains acyclicity after
restricting to each chart. Native dimension shifting gives vanishing
of all positive étale cohomology.
-/

namespace ManuscriptAudit.FieldEtaleCohomologyAcyclic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleObjectRestriction FieldEtaleGaloisCovers GaloisCoverAction
open FieldEtaleSkyscraperResolution

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev X := Spec (CommRingCat.of K)
private abbrev D := Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}

/-- Every finite Galois section representation on every actual étale
field chart has zero positive cohomology. -/
def HasAcyclicGaloisSections (A : D K) : Prop :=
  ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [Module.Finite F L] [IsGalois F L]
    (j : Spec (CommRingCat.of F) ⟶ X K) [Etale j] (n : ℕ),
    IsZero (groupCohomology (sectionsRep F L ((restriction j).obj A)) (n + 1))

theorem HasAcyclicGaloisSections.chartHOne {A : D K}
    (hA : HasAcyclicGaloisSections K A) (F : Type) [Field F]
    (j : Spec (CommRingCat.of F) ⟶ X K) [Etale j] :
    Subsingleton (Sheaf.H ((restriction j).obj A) 1) :=
  FieldEtaleHOneDetection.HOne_subsingleton_of_finiteGalois F ((restriction j).obj A)
    (fun L ↦ ModuleCat.subsingleton_of_isZero (hA F L j 0))

private def cokernelSequence (A : D K) : ShortComplex (D K) :=
  ShortComplex.cokernelSequence (injectivePresentation K A).f

private theorem cokernelSequence_shortExact (A : D K) :
    (cokernelSequence K A).ShortExact := by
  let I := injectivePresentation K A
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact I.f)
    (inferInstanceAs (Mono I.f)) (inferInstanceAs (Epi (cokernel.π I.f)))

set_option maxHeartbeats 3200000 in
/-- Quotienting an injective geometric skyscraper by a sheaf with
acyclic Galois sections preserves their acyclicity on all field charts. -/
theorem quotient_hasAcyclicGaloisSections (A : D K) (hA : HasAcyclicGaloisSections K A) :
    HasAcyclicGaloisSections K (cokernelSequence K A).X₃ := by
  intro F L _ _ _ _ _ j _ n
  let S := cokernelSequence K A
  have hS : S.ShortExact := cokernelSequence_shortExact K A
  let R := restriction j
  letI : R.IsLeftAdjoint := (restrictionAdjunction j).isLeftAdjoint
  letI : PreservesFiniteLimits R := restriction_preservesFiniteLimits j
  letI : R.Additive := R.additive_of_preserves_binary_products
  let S' := S.map R
  have hS' : S'.ShortExact := hS.map_of_exact R
  have hSurj : Function.Surjective (S'.g.hom.app (op (galoisObject F L))) := by
    change Function.Surjective
      (S.g.hom.app (op ((postcompose j).obj (galoisObject F L))))
    exact sections_surjective_of_HOne_of_field S hS ((postcompose j).obj (galoisObject F L))
      L (Iso.refl _) (fun j' _ ↦ HasAcyclicGaloisSections.chartHOne K hA L j')
  let T := sectionSequence F L S'
  have hT : T.ShortExact := sectionSequence_shortExact F L S' hS' hSurj
  have hMiddle : IsZero (groupCohomology T.X₂ (n + 1)) := by
    change IsZero (groupCohomology (sectionsRep F L
      (R.obj (injectivePresentation K A).J)) (n + 1))
    rw [injectivePresentation_J]
    exact GaloisSkyscraperSectionCohomology.sections_H_succ_isZero
      (geometricPoint K) F L j (injectiveCoefficient K A) n
  have hFirst : IsZero (groupCohomology T.X₁ ((n + 1) + 1)) :=
    hA F L j (n + 1)
  exact (groupCohomology.mapShortComplex₃_exact hT (i := n + 1) (j := (n + 1) + 1)
    rfl).isZero_of_both_isZero hMiddle hFirst

/-- All positive native small-étale cohomology vanishes when the
coefficient sheaf has acyclic finite Galois sections on every field chart. -/
theorem H_succ_subsingleton (A : D K) (hA : HasAcyclicGaloisSections K A) (n : ℕ) :
    Subsingleton (Sheaf.H A (n + 1)) := by
  induction n generalizing A with
  | zero =>
    have h := HasAcyclicGaloisSections.chartHOne K hA K (𝟙 (X K))
    let e := ((Sheaf.functorH (X K).smallEtaleTopology 1).mapIso
      (restrictionIdentityIso A)).addCommGroupIsoToAddEquiv
    exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩
  | succ n ih =>
    let T := cokernelSequence K A
    have hT : T.ShortExact := cokernelSequence_shortExact K A
    letI : Injective T.X₂ := (injectivePresentation K A).injective
    have hQ : Subsingleton (Sheaf.H T.X₃ (n + 1)) :=
      ih T.X₃ (quotient_hasAcyclicGaloisSections K A hA)
    exact SheafCohomologyDimensionShift.H_succ_subsingleton_of_injectiveMiddle T hT (n + 1) hQ

end

end ManuscriptAudit.FieldEtaleCohomologyAcyclic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FieldEtaleCohomologyAcyclic.quotient_hasAcyclicGaloisSections,
      ``ManuscriptAudit.FieldEtaleCohomologyAcyclic.H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
