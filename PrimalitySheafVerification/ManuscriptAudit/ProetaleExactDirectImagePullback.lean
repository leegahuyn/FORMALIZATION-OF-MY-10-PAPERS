import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImageCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeCohomologyPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! The exact direct-image comparison is the literal pullback of the
coefficient morphism on the scheme's native pro-étale cohomology. -/

namespace ManuscriptAudit.ProetaleExactDirectImagePullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ProetaleBaseChange (directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleSchemeCohomologyPullback (mapOfDirectImage)
open ProetaleExactDirectImageCohomology (cohomologyEquiv)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private abbrev A := AddCommGrpCat.{u + 1}
private abbrev C (X : Scheme.{u}) := Sheaf (Scheme.ProEt.topology X) A.{u}

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [hE : (directImage f A.{u}).PreservesEpimorphisms]

include hE

set_option maxHeartbeats 6900000 in
/-- The exact direct-image comparison of the actual coefficient arrow is the native pullback. -/
theorem pullback_eq {V : C Y} {W : C X} (a : V ⟶ (directImage f A.{u}).obj W)
    (n : ℕ) (x : Sheaf.H V n) :
    mapOfDirectImage f a n x = cohomologyEquiv f W n (Sheaf.H.map a n x) := by
  let L := inverseImage f
  let b := ((adjunction f).homEquiv V W).symm a
  let c := (adjunction f).counit.app W
  let i := (constantInverseImageIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hb : b = L.map a ≫ c := (adjunction f).homEquiv_counit V W a
  change ((Ext.mk₀ i.inv).comp (x.mapExactFunctor L) (zero_add n)).comp
      (Ext.mk₀ b) (add_zero n) =
    (Ext.mk₀ i.inv).comp
      (((x.comp (Ext.mk₀ a) (add_zero n)).mapExactFunctor L).comp
        (Ext.mk₀ c) (add_zero n)) (zero_add n)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hb]

/-- When the literal coefficient arrow to the direct image is an isomorphism,
the actual native pullback is bijective in every degree. -/
theorem pullback_bijective {V : C Y} {W : C X} (a : V ⟶ (directImage f A.{u}).obj W)
    [IsIso a] (n : ℕ) : Function.Bijective (mapOfDirectImage f a n) := by
  let E := (cohomologyIso (asIso a) n).trans (cohomologyEquiv f W n)
  have h : ⇑(mapOfDirectImage f a n) = ⇑E := funext (pullback_eq f a n)
  rw [h]
  exact E.bijective

end
end ManuscriptAudit.ProetaleExactDirectImagePullback

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleExactDirectImagePullback.pullback_bijective
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
