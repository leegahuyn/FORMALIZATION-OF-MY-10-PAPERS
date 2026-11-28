import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtExactAdjunctionBijective
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! When the actual native direct image preserves epimorphisms,
its genuine comparison computes all degrees of native cohomology. -/

namespace ManuscriptAudit.ProetaleExactDirectImageCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ProetaleBaseChange (directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleContinuousDirectImageMaps (functions functionsOver)

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
/-- Exact native direct image and its exact inverse image identify the
actual cohomology groups, by the original comparison map in every degree. -/
def cohomologyEquiv (T : C X) (n : ℕ) :
    Sheaf.H ((R f).obj T) n ≃+ Sheaf.H T n := by
  let L := inverseImage f
  let E := R f
  let a := adjunction f
  letI : E.IsRightAdjoint := a.isRightAdjoint
  letI : PreservesLimits E := a.rightAdjoint_preservesLimits
  letI : E.Additive := E.additive_of_preserves_binary_products
  letI : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  letI : PreservesFiniteColimits E := Functor.preservesFiniteColimits_of_preservesHomology E
  letI : EnoughInjectives (C X) := IsGrothendieckAbelian.enoughInjectives.{u + 1} (C := C X)
  let j : L.obj (Z Y) ≅ Z X :=
    (constantInverseImageIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let e := AddEquiv.ofBijective (ExtExactAdjunctionMap.map a (Z Y) T n)
    (ExtExactAdjunctionBijective.bijective a (Z Y) n T)
  let k : Ext (L.obj (Z Y)) T n ≃+ Sheaf.H T n :=
    { toFun := (Ext.mk₀ j.inv).precomp T (zero_add n)
      invFun := (Ext.mk₀ j.hom).precomp T (zero_add n)
      left_inv := by
        intro x
        change (Ext.mk₀ j.hom).comp ((Ext.mk₀ j.inv).comp x (zero_add n)) (zero_add n) = x
        rw [Ext.mk₀_comp_mk₀_assoc, j.hom_inv_id, Ext.mk₀_id_comp]
      right_inv := by
        intro x
        change (Ext.mk₀ j.inv).comp ((Ext.mk₀ j.hom).comp x (zero_add n)) (zero_add n) = x
        rw [Ext.mk₀_comp_mk₀_assoc, j.inv_hom_id, Ext.mk₀_id_comp]
      map_add' := fun x y ↦ map_add ((Ext.mk₀ j.inv).precomp T (zero_add n)) x y }
  exact e.trans k

/-- Apply the actual comparison to a continuous coefficient system. -/
def continuousEquiv {U V : Scheme.{0}} (g : U ⟶ V)
    [(directImage g AddCommGrpCat.{1}).PreservesEpimorphisms]
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (n : ℕ) : Sheaf.H (functionsOver M g) n ≃+ Sheaf.H (functions M U) n :=
  cohomologyEquiv g (functions M U) n

end
end ManuscriptAudit.ProetaleExactDirectImageCohomology

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleExactDirectImageCohomology.cohomologyEquiv
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
