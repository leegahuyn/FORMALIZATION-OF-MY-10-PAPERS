import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionComplexZeroKernel

/-! The actual integer-indexed section complex computes natural degree-zero sheaf cohomology. -/

namespace ManuscriptAudit.SheafSectionComplexZeroComparison

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SheafSectionResolutionComplex (sections sectionComplex sectionComplexMap)
open SheafSectionComplexZeroKernel (negativeTerm_isZero zeroInclusion inclusionIsKernel zeroInclusion_natural)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{0}

variable [HasSheafify J A] [EnoughInjectives (Sheaf J A)]
variable (T : C)

private def cyclesKernel (F : Sheaf J A) :=
  (sectionComplex J T F).cyclesIsKernel 0 1 (by simp)

private def sectionsToCycles (F : Sheaf J A) :
    (sections J T).obj F ≅ (sectionComplex J T F).cycles 0 :=
  (inclusionIsKernel J T F).conePointUniqueUpToIso (cyclesKernel J T F)

@[reassoc]
private theorem sectionsToCycles_fac (F : Sheaf J A) :
    (sectionsToCycles J T F).hom ≫ (sectionComplex J T F).iCycles 0 = zeroInclusion J T F :=
  IsLimit.conePointUniqueUpToIso_hom_comp (inclusionIsKernel J T F)
    (cyclesKernel J T F) WalkingParallelPair.zero

private theorem sectionsToCycles_natural {F G : Sheaf J A} (f : F ⟶ G) :
    (sections J T).map f ≫ (sectionsToCycles J T G).hom =
      (sectionsToCycles J T F).hom ≫ cyclesMap (sectionComplexMap J T f) 0 := by
  apply (cancel_mono ((sectionComplex J T G).iCycles 0)).mp
  simpa only [Category.assoc, sectionsToCycles_fac, cyclesMap_i,
    sectionsToCycles_fac_assoc] using (zeroInclusion_natural J T f).symm

private theorem incoming_zero (F : Sheaf J A) : ((sectionComplex J T F).sc 0).f = 0 := by
  have h : IsZero (((sectionComplex J T F).sc 0).X₁) := by
    change IsZero ((sectionComplex J T F).X ((ComplexShape.up ℤ).prev 0))
    simpa using negativeTerm_isZero J T F (-1) (by decide)
  exact h.eq_of_src _ _

/-- The actual zeroth cohomology is naturally isomorphic to the terminal sections. -/
def fromSections (F : Sheaf J A) :
    (sections J T).obj F ≅ (sectionComplex J T F).homology 0 :=
  sectionsToCycles J T F ≪≫ ((sectionComplex J T F).sc 0).asIsoHomologyπ (incoming_zero J T F)

theorem fromSections_natural {F G : Sheaf J A} (f : F ⟶ G) :
    (sections J T).map f ≫ (fromSections J T G).hom =
      (fromSections J T F).hom ≫ homologyMap (sectionComplexMap J T f) 0 := by
  change (sections J T).map f ≫ ((sectionsToCycles J T G).hom ≫
      (sectionComplex J T G).homologyπ 0) =
    ((sectionsToCycles J T F).hom ≫ (sectionComplex J T F).homologyπ 0) ≫
      homologyMap (sectionComplexMap J T f) 0
  rw [← Category.assoc, sectionsToCycles_natural, Category.assoc,
    Category.assoc, homologyπ_naturality]

variable [HasExt.{0} (Sheaf J A)]
variable {T} (hT : IsTerminal T)

/-- The actual zeroth section-complex cohomology agrees with native sheaf cohomology. -/
def cohomologyEquiv (F : Sheaf J A) :
    (sectionComplex J T F).homology 0 ≃+ Sheaf.H F 0 :=
  (fromSections J T F).symm.addCommGroupIsoToAddEquiv.trans (Sheaf.H.equiv₀ F hT).symm

/-- This zeroth comparison sends the actual lifted map to the native sheaf cohomology map. -/
theorem cohomologyEquiv_natural {F G : Sheaf J A} (f : F ⟶ G)
    (x : (sectionComplex J T F).homology 0) :
    cohomologyEquiv J hT G (homologyMap (sectionComplexMap J T f) 0 x) =
      Sheaf.H.map f 0 (cohomologyEquiv J hT F x) := by
  let e₀ := (fromSections J T F).addCommGroupIsoToAddEquiv
  let e₁ := (fromSections J T G).addCommGroupIsoToAddEquiv
  apply (Sheaf.H.equiv₀ G hT).injective
  change (Sheaf.H.equiv₀ G hT) ((Sheaf.H.equiv₀ G hT).symm
      (e₁.symm (homologyMap (sectionComplexMap J T f) 0 x))) =
    (Sheaf.H.equiv₀ G hT) (Sheaf.H.map f 0 ((Sheaf.H.equiv₀ F hT).symm (e₀.symm x)))
  rw [AddEquiv.apply_symm_apply, ← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  apply e₁.injective
  rw [AddEquiv.apply_symm_apply]
  have h := CategoryTheory.congr_fun (fromSections_natural J T f) (e₀.symm x)
  change e₁ ((sections J T).map f (e₀.symm x)) =
    homologyMap (sectionComplexMap J T f) 0 (e₀ (e₀.symm x)) at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

end
end ManuscriptAudit.SheafSectionComplexZeroComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafSectionComplexZeroComparison.fromSections,
      ``ManuscriptAudit.SheafSectionComplexZeroComparison.fromSections_natural,
      ``ManuscriptAudit.SheafSectionComplexZeroComparison.cohomologyEquiv,
      ``ManuscriptAudit.SheafSectionComplexZeroComparison.cohomologyEquiv_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
