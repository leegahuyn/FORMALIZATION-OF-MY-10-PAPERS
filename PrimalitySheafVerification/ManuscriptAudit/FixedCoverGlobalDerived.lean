import Lean.Util.CollectAxioms
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finsupp.Single
import PrimalitySheafVerification.ManuscriptAudit.FixedCoverCechCounterexample

/-!
On the top open of a topological space, the two native presentations
of sheaf cohomology are equivalent. For Paper 4, physical p. 114,
this identifies the nonzero degree-one group of the fixed-cover
counterexample with the Ext¹-group from the constant integer sheaf.
-/

namespace ManuscriptAudit.FixedCoverGlobalDerived

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.TwoOpenDerivedComparison ManuscriptAudit.FixedCoverCechCounterexample

noncomputable section

set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1200000

private abbrev G := AddCommGrpCat.{0}
local notation "D" => PrimeSpectrum.basicOpen (R := ℤ)

local instance (X : TopCat.{0}) : HasExt.{0} (Sheaf (Opens.grothendieckTopology X) G) :=
  IsGrothendieckAbelian.hasExt _

/-- The representable presheaf of the largest open is the constant singleton. -/
private def terminalYonedaIso (X : TopCat.{0}) :
    yoneda.obj (⊤ : Opens X) ≅ (Functor.const (Opens X)ᵒᵖ).obj (PUnit : Type) := by
  refine NatIso.ofComponents (fun U => ?_) ?_
  · let e : (unop U ⟶ (⊤ : Opens X)) ≃ (PUnit : Type) :=
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => homOfLE le_top
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
    exact e.toIso
  · intro U V f
    ext x <;> rfl

private def freeSingletonIso :
    AddCommGrpCat.free.obj (PUnit : Type) ≅ AddCommGrpCat.of (ULift.{0} ℤ) := by
  let e : (PUnit →₀ ℤ) ≃+ ℤ :=
    { toEquiv := Finsupp.uniqueEquiv PUnit.unit
      map_add' := fun _ _ => rfl }
  exact ((FreeAbelianGroup.equivFinsupp PUnit).trans
    (e.trans (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).symm)).toAddCommGrpIso

/-- For the terminal open, the native cohomology in an object is the
native global Ext from the constant integer sheaf. -/
def derivedOnTopEquivGlobal {X : TopCat.{0}} (F : Sheaf (Opens.grothendieckTopology X) G) (n : ℕ) :
    F.H' n (⊤ : Opens X) ≃+ F.H n := by
  let i : ((Functor.const (Opens X)ᵒᵖ).obj (PUnit : Type) ⋙ AddCommGrpCat.free) ≅
      (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
    NatIso.ofComponents (fun _ => freeSingletonIso) (by
      intro U V f
      change AddCommGrpCat.free.map (𝟙 (PUnit : Type)) ≫ freeSingletonIso.hom =
        freeSingletonIso.hom ≫ 𝟙 _
      rw [Functor.map_id, Category.id_comp, Category.comp_id])
  let j := (presheafToSheaf (Opens.grothendieckTopology X) G).mapIso
    ((Functor.isoWhiskerRight (terminalYonedaIso X) AddCommGrpCat.free).trans i)
  exact (((extFunctor n).mapIso j.op).app F).addCommGroupIsoToAddEquiv.symm

theorem boundarySheaf_globalDerivedH1_nontrivial : Nontrivial (boundarySheaf.H 1) := by
  letI := boundarySheaf_derivedH1_nontrivial
  exact (derivedOnTopEquivGlobal (X := TopCat.of (PrimeSpectrum ℤ)) boundarySheaf 1).injective.nontrivial

/-- The same failure, with the global derived group written literally
as Ext¹ from the constant integer sheaf. -/
theorem paper4_fixedCoverCech_not_globalDerivedH1 :
    ¬ Nonempty
      (((boundarySheaf.obj.obj (op (D 2 ⊓ D 3))) ⧸
        (twoOpenDifferential boundarySheaf.obj (D 2) (D 3)).range) ≃+
        boundarySheaf.H 1) := by
  rintro ⟨e⟩
  exact paper4_fixedCoverCech_not_derivedH1
    ⟨e.trans (derivedOnTopEquivGlobal (X := TopCat.of (PrimeSpectrum ℤ)) boundarySheaf 1).symm⟩

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``derivedOnTopEquivGlobal, ``boundarySheaf_globalDerivedH1_nontrivial,
      ``paper4_fixedCoverCech_not_globalDerivedH1] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.FixedCoverGlobalDerived
