import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import PrimalitySheafVerification.ManuscriptAudit.SheafTerminalSectionsAsHoms

/-! Positive Ext of an abelian sheaf from the actual sections of its injective resolution. -/

namespace ManuscriptAudit.SheafPositiveResolutionCohomology

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open SheafTerminalSectionsAsHoms (sections integers homEquiv homEquiv_comp homEquiv_symm_map)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{0}

variable [HasSheafify J A] [HasExt.{0} (Sheaf J A)]

local instance sections_additive (T : C) : (sections J T).Additive :=
  ⟨by intros; rfl⟩

variable {T : C} (hT : IsTerminal T)

variable {F : Sheaf J A} (R : InjectiveResolution F)

/-- Three successive terms of the actual evaluated resolution in a positive degree. -/
def sectionsShort (n : ℕ) : ShortComplex A :=
  ShortComplex.mk
    ((sections J T).map (R.cocomplex.d n (n + 1)))
    ((sections J T).map (R.cocomplex.d (n + 1) (n + 2)))
    (by rw [← Functor.map_comp, R.cocomplex.d_comp_d, Functor.map_zero])

private abbrev Γ (n : ℕ) :=
  (homEquiv J hT (R.cocomplex.X n)).symm

private theorem cycle_comp_zero (n : ℕ) (x : (sectionsShort J R n (T := T)).g.hom.ker) :
    Γ J hT R (n + 1) (x : (sectionsShort J R n (T := T)).X₂) ≫
      R.cocomplex.d (n + 1) (n + 2) = 0 := by
  rw [← homEquiv_symm_map J hT]
  have hx : (sections J T).map (R.cocomplex.d (n + 1) (n + 2)) x.val = 0 := x.property
  rw [hx, map_zero]

/-- Each cycle of the section complex represents the actual native Ext class. -/
def cycleClass (n : ℕ) :
    (sectionsShort J R n (T := T)).g.hom.ker →+ Sheaf.H F (n + 1) where
  toFun x := R.extMk (Γ J hT R (n + 1) x.val) (n + 2) rfl (cycle_comp_zero J hT R n x)
  map_zero' := by
    change R.extMk (Γ J hT R (n + 1) 0) (n + 2) rfl _ = 0
    simpa only [map_zero] using (R.extMk_zero (X := integers J) (n + 2) rfl)
  map_add' x y := by
    change R.extMk (Γ J hT R (n + 1) (x.val + y.val)) (n + 2) rfl _ =
      R.extMk (Γ J hT R (n + 1) x.val) (n + 2) rfl _ +
      R.extMk (Γ J hT R (n + 1) y.val) (n + 2) rfl _
    simpa only [map_add] using (R.add_extMk (Γ J hT R (n + 1) x.val)
      (Γ J hT R (n + 1) y.val) (n + 2) rfl (cycle_comp_zero J hT R n x)
      (cycle_comp_zero J hT R n y)).symm

theorem cycleClass_surjective (n : ℕ) : Function.Surjective (cycleClass J hT R n) := by
  intro x
  obtain ⟨f, hf, hfx⟩ := R.extMk_surjective x (n + 2) (show n + 1 + 1 = n + 2 from rfl)
  let a := homEquiv J hT (R.cocomplex.X (n + 1))
  let v := a f
  have hv : (sectionsShort J R n (T := T)).g.hom v = 0 := by
    change (sections J T).map (R.cocomplex.d (n + 1) (n + 2)) (a f) = 0
    rw [← homEquiv_comp, hf, map_zero]
  refine ⟨⟨v, hv⟩, ?_⟩
  change R.extMk (a.symm (a f)) (n + 2) rfl _ = x
  simpa only [AddEquiv.symm_apply_apply] using hfx

/-- A cycle represents zero exactly when it is a boundary in the evaluated resolution. -/
theorem cycleClass_kernel (n : ℕ) :
    (cycleClass J hT R n).ker = (sectionsShort J R n (T := T)).abToCycles.range := by
  ext x
  change R.extMk (Γ J hT R (n + 1) x.val) (n + 2) rfl (cycle_comp_zero J hT R n x) = 0 ↔
    x ∈ (sectionsShort J R n (T := T)).abToCycles.range
  rw [R.extMk_eq_zero_iff _ _ rfl _ n rfl, AddMonoidHom.mem_range]
  let a := homEquiv J hT (R.cocomplex.X n)
  let b := homEquiv J hT (R.cocomplex.X (n + 1))
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨a f, Subtype.ext ?_⟩
    change (sections J T).map (R.cocomplex.d n (n + 1)) (a f) = x.val
    rw [← homEquiv_comp, hf, b.apply_symm_apply]
  · rintro ⟨y, hy⟩
    refine ⟨a.symm y, ?_⟩
    have h := congrArg Subtype.val hy
    change (sections J T).map (R.cocomplex.d n (n + 1)) y = x.val at h
    rw [← homEquiv_symm_map J hT, h]

/-- Homology of the actual evaluated three-term complex is native positive sheaf cohomology. -/
def positiveEquiv (n : ℕ) :
    (sectionsShort J R n (T := T)).homology ≃+ Sheaf.H F (n + 1) :=
  (sectionsShort J R n (T := T)).abHomologyIso.addCommGroupIsoToAddEquiv.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (cycleClass_kernel J hT R n).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (cycleClass_surjective J hT R n)))

end
end ManuscriptAudit.SheafPositiveResolutionCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafPositiveResolutionCohomology.cycleClass,
      ``ManuscriptAudit.SheafPositiveResolutionCohomology.cycleClass_surjective,
      ``ManuscriptAudit.SheafPositiveResolutionCohomology.cycleClass_kernel,
      ``ManuscriptAudit.SheafPositiveResolutionCohomology.positiveEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
