import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.MorphismProperty.Comma
import PrimalitySheafVerification.ManuscriptAudit.AffineCechConerveSpecLimit
import PrimalitySheafVerification.ManuscriptAudit.CechNervePreservedWideCone

/-! The spectrum of the affine conerve is the actual Čech nerve in
either site, with the literal structure maps and vertex projections. -/

namespace ManuscriptAudit.AffineCechConerveSiteComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineCechConerveSpecLimit (degree specCone isLimit_specCone specCone_π specCone_base)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : CommRingCat.{u}} (P : MorphismProperty Scheme.{u})

abbrev Site := P.Over ⊤ (Spec A)

abbrev forget : Site (A := A) P ⥤ Scheme :=
  MorphismProperty.Over.forget P ⊤ (Spec A) ⋙ Over.forget (Spec A)

abbrev chart (R : Under A) (h : P (Spec.map R.hom)) : Site (A := A) P :=
  MorphismProperty.Over.mk _ (Spec.map R.hom) h

abbrev map {U V : Under A} (m : U ⟶ V)
    (hU : P (Spec.map U.hom)) (hV : P (Spec.map V.hom)) : chart P V hV ⟶ chart P U hU :=
  MorphismProperty.Over.homMk (Spec.map m.right) (by
    change Spec.map m.right ≫ Spec.map U.hom = Spec.map V.hom
    rw [← Spec.map_comp, Under.w m])

variable [HasFiniteLimits (Site (A := A) P)]
  [∀ n : ℕ, PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1))) (forget (A := A) P)]

variable (f : Arrow (Under A))
  (hL : P (Spec.map f.left.hom)) (hR : P (Spec.map f.right.hom)) (n : ℕ)

abbrev siteMap := map P f.hom hL hR

abbrev native := CechNerveLowDegrees.N (siteMap P f hL hR) n

private abbrev wideCone := CechNervePreservedWideCone.cone (forget P) (siteMap P f hL hR) n

/-- The spectral cone point is identified with the literal site Čech term. -/
def schemeIso : Spec (degree f n).right ≅ (native P f hL hR n).left :=
  (isLimit_specCone f n).conePointUniqueUpToIso
    (CechNervePreservedWideCone.isLimit_cone (forget P) (siteMap P f hL hR) n)

theorem schemeIso_vertex (i : Fin (n + 1)) :
    (schemeIso P f hL hR n).hom ≫ (CechNerveLowDegrees.vertex (siteMap P f hL hR) n i).left =
      Spec.map (AffineCechConerveSpecLimit.vertex f n i).right := by
  have h := (isLimit_specCone f n).conePointUniqueUpToIso_hom_comp
    (CechNervePreservedWideCone.isLimit_cone (forget P) (siteMap P f hL hR) n) (some i)
  change (schemeIso P f hL hR n).hom ≫ (wideCone P f hL hR n).π i = (specCone f n).π i at h
  rw [CechNervePreservedWideCone.cone_π, specCone_π] at h
  exact h

theorem schemeIso_over :
    (schemeIso P f hL hR n).hom ≫ (native P f hL hR n).hom = Spec.map (degree f n).hom := by
  let j := CechNerveLowDegrees.vertex (siteMap P f hL hR) n 0
  have hj : j.left ≫ Spec.map f.right.hom = (native P f hL hR n).hom :=
    MorphismProperty.Over.w j
  rw [← hj, ← Category.assoc, schemeIso_vertex, ← Spec.map_comp, Under.w]

variable [P.RespectsIso]

include hL hR in
/-- The genuine affine algebra nerve has the actual structural property
in every degree, by its proved isomorphism over the original base. -/
theorem property_degree : P (Spec.map (degree f n).hom) := by
  rw [← schemeIso_over P f hL hR n]
  exact (P.cancel_left_of_respectsIso _ _).mpr (native P f hL hR n).prop

/-- The comparison is an isomorphism in the actual small site. -/
def siteIso : chart P (degree f n) (property_degree P f hL hR n) ≅ native P f hL hR n :=
  MorphismProperty.Over.isoMk (schemeIso P f hL hR n) (schemeIso_over P f hL hR n)

end
end ManuscriptAudit.AffineCechConerveSiteComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineCechConerveSiteComparison.property_degree,
      ``ManuscriptAudit.AffineCechConerveSiteComparison.siteIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
