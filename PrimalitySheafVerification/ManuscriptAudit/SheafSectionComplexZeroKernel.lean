import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionResolutionComplex

/-! The actual injective-section complex is zero below degree zero and has the correct initial kernel. -/

namespace ManuscriptAudit.SheafSectionComplexZeroKernel

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SheafSectionResolutionComplex (sections resolution resolutionMap sectionComplex sectionComplexMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{0}

variable [HasSheafify J A] [EnoughInjectives (Sheaf J A)]
variable (T : C)

theorem negativeTerm_isZero (F : Sheaf J A) (i : ℤ) (hi : i < 0) :
    IsZero ((sectionComplex J T F).X i) :=
  (sections J T).map_isZero ((resolution J F).cochainComplex.isZero_of_isStrictlyGE 0 i hi)

/-- The actual section complex has no negative cohomology. -/
theorem negativeHomology_subsingleton (F : Sheaf J A) (i : ℤ) (hi : i < 0) :
    Subsingleton ((sectionComplex J T F).homology i) :=
  AddCommGrpCat.subsingleton_of_isZero
    ((ExactAt.of_isZero (negativeTerm_isZero J T F i hi)).isZero_homology)

private def termIso (F : Sheaf J A) (i : ℕ) :
    (sectionComplex J T F).X (i : ℤ) ≅ (sections J T).obj (resolution J F).cocomplex.X i :=
  (sections J T).mapIso ((resolution J F).cochainComplexXIso (i : ℤ) i rfl)

/-- The actual degree-zero section of the resolution augmentation. -/
def zeroInclusion (F : Sheaf J A) :
    (sections J T).obj F ⟶ (sectionComplex J T F).X 0 :=
  (sections J T).map ((resolution J F).ι.f 0) ≫ (termIso J T F 0).inv

private theorem differential_square (F : Sheaf J A) :
    (termIso J T F 0).inv ≫ (sectionComplex J T F).d 0 1 =
      (sections J T).map ((resolution J F).cocomplex.d 0 1) ≫ (termIso J T F 1).inv := by
  let R := resolution J F
  let E := sections J T
  change E.map (R.cochainComplexXIso 0 0 rfl).inv ≫ E.map (R.cochainComplex.d 0 1) =
    E.map (R.cocomplex.d 0 1) ≫ E.map (R.cochainComplexXIso 1 1 rfl).inv
  rw [← Functor.map_comp, ← Functor.map_comp, R.cochainComplex_d 0 1 0 1 rfl rfl]
  simp only [Iso.inv_hom_id_assoc]

private theorem zeroInclusion_comp_d (F : Sheaf J A) :
    zeroInclusion J T F ≫ (sectionComplex J T F).d 0 1 = 0 := by
  let R := resolution J F
  let E := sections J T
  change (E.map (R.ι.f 0) ≫ (termIso J T F 0).inv) ≫ (sectionComplex J T F).d 0 1 = 0
  rw [Category.assoc, differential_square, ← Category.assoc, ← Functor.map_comp,
    R.ι_f_zero_comp_complex_d, Functor.map_zero, zero_comp]

/-- Evaluated augmentation is the actual degree-zero kernel of the section complex. -/
def inclusionIsKernel (F : Sheaf J A) :
    IsLimit (KernelFork.ofι (zeroInclusion J T F) (zeroInclusion_comp_d J T F)) := by
  let R := resolution J F
  let E := sections J T
  let hR := R.kernelFork.mapIsLimit R.isLimitKernelFork E
  exact IsKernel.ofIso hR _ (termIso J T F 0).symm (termIso J T F 1).symm (Iso.refl _)
    (differential_square J T F) (by simp [zeroInclusion])

/-- The actual resolved augmentation is natural in the sheaf morphism. -/
theorem zeroInclusion_natural {F G : Sheaf J A} (f : F ⟶ G) :
    zeroInclusion J T F ≫ (sectionComplexMap J T f).f 0 =
      (sections J T).map f ≫ zeroInclusion J T G := by
  let R := resolution J F
  let P := resolution J G
  let φ := resolutionMap J f
  let E := sections J T
  change (E.map (R.ι.f 0) ≫ E.map (R.cochainComplexXIso 0 0 rfl).inv) ≫
    E.map (φ.hom'.f 0) =
      E.map f ≫ (E.map (P.ι.f 0) ≫ E.map (P.cochainComplexXIso 0 0 rfl).inv)
  simp only [← Functor.map_comp]
  rw [φ.hom'_f 0 0 rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, InjectiveResolution.desc_commutes_zero, Category.assoc]

end
end ManuscriptAudit.SheafSectionComplexZeroKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafSectionComplexZeroKernel.negativeHomology_subsingleton,
      ``ManuscriptAudit.SheafSectionComplexZeroKernel.inclusionIsKernel,
      ``ManuscriptAudit.SheafSectionComplexZeroKernel.zeroInclusion_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
