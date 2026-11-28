import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImageCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicDirectImageScalar

/-! The actual naturality of exact pro-étale direct-image comparison,
including its compatibility with the intrinsic continuous scalar action. -/

namespace ManuscriptAudit.ProetaleExactDirectImageNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open ProetaleBaseChange (directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleContinuousDirectImageMaps (functionsOver)
open ProetaleExactDirectImageCohomology (cohomologyEquiv continuousEquiv)
open NativeAdicScalarAction (adicModule scalarMap)
open ProetaleAdicDirectImageScalar (imageModule scalar)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev A := AddCommGrpCat.{u + 1}
private abbrev C (Z : Scheme.{u}) := Sheaf (Scheme.ProEt.topology Z) A.{u}
private abbrev Z (T : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology T) A.{u}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))
private abbrev R := directImage f A.{u}

variable [(R f).PreservesEpimorphisms]

set_option maxHeartbeats 6500000 in
/-- The native all-degree comparison commutes with coefficient maps. -/
theorem natural {U V : C X} (g : U ⟶ V) (n : ℕ)
    (x : Sheaf.H ((R f).obj U) n) :
    cohomologyEquiv f V n (Sheaf.H.map ((R f).map g) n x) =
      Sheaf.H.map g n (cohomologyEquiv f U n x) := by
  let j : (inverseImage f).obj (Z Y) ≅ Z X :=
    (constantInverseImageIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let c (T : C X) := ExtExactAdjunctionMap.map (adjunction f) (Z Y) T n
  change (Ext.mk₀ j.inv).comp
      (c V (x.comp (Ext.mk₀ ((R f).map g)) (add_zero n))) (zero_add n) =
      ((Ext.mk₀ j.inv).comp (c U x) (zero_add n)).comp (Ext.mk₀ g) (add_zero n)
  have h := ExtExactAdjunctionMap.map_naturality (adjunction f) (Z Y) g n x
  change c V (x.comp (Ext.mk₀ ((R f).map g)) (add_zero n)) =
    (c U x).comp (Ext.mk₀ g) (add_zero n) at h
  rw [h, Ext.comp_assoc_of_third_deg_zero]

section Adic

variable {U V : Scheme.{0}} (i : U ⟶ V)
  [(directImage i AddCommGrpCat.{1}).PreservesEpimorphisms]
  (l d : ℕ) [Fact l.Prime]

local instance : Module ℤ_[l] (Sheaf.H (functionsOver ℤ_[l] i) d) := imageModule i l d
local instance : Module ℤ_[l] (U.EllAdicCohomology l d) := adicModule U l d

/-- The same actual comparison is linear for the intrinsic adic actions. -/
def adicLinearEquiv :
    Sheaf.H (functionsOver ℤ_[l] i) d ≃ₗ[ℤ_[l]] U.EllAdicCohomology l d where
  __ := continuousEquiv i ℤ_[l] d
  map_smul' a x := by
    change continuousEquiv i ℤ_[l] d (Sheaf.H.map (scalar i l a) d x) =
      Sheaf.H.map (scalarMap U l a) d (continuousEquiv i ℤ_[l] d x)
    exact natural i (scalarMap U l a) d x

end Adic
end
end ManuscriptAudit.ProetaleExactDirectImageNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleExactDirectImageNaturality.natural,
      ``ManuscriptAudit.ProetaleExactDirectImageNaturality.adicLinearEquiv] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
