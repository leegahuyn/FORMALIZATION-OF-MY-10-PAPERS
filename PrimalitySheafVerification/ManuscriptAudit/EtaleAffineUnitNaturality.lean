import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Units.Equiv
import PrimalitySheafVerification.ManuscriptAudit.EtaleCohomologyPresheafZero

/-! The native zero-degree unit restriction, expressed in the coordinate
rings of affine étale objects, is literally the induced map of units. -/

namespace ManuscriptAudit.EtaleAffineUnitNaturality

open AlgebraicGeometry CategoryTheory
open EtaleCohomologyPresheafZero KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {X : Scheme.{0}} {U V : X.Etale} {R S : CommRingCat.{0}}

/-- Implementation of global sections in any specified affine coordinate chart. -/
def sectionIso {T : Scheme.{0}} (e : T ≅ Spec R) : Γ(T, ⊤) ≅ R :=
  { hom := e.inv.appTop
    inv := e.hom.appTop
    hom_inv_id := by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
    inv_hom_id := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop] } ≪≫
    Scheme.ΓSpecIso R

theorem sectionIso_naturality (m : U ⟶ V) (eU : U.left ≅ Spec R) (eV : V.left ≅ Spec S)
    (f : S ⟶ R) (h : eU.inv ≫ m.left = Spec.map f ≫ eV.inv) :
    m.left.appTop ≫ (sectionIso eU).hom = (sectionIso eV).hom ≫ f := by
  change m.left.appTop ≫ (eU.inv.appTop ≫ (Scheme.ΓSpecIso R).hom) =
    (eV.inv.appTop ≫ (Scheme.ΓSpecIso S).hom) ≫ f
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]

/-- The actual ambient H′⁰ group on an affine étale object is the
multiplicative coordinate-ring unit group, written additively. -/
def coordinateUnitEquiv (e : U.left ≅ Spec R) :
    (fullCoordinateUnitSheaf X).H' 0 U ≃+ Additive Rˣ :=
  (unitEquivZero U).trans
    (Units.mapEquiv (sectionIso e).commRingCatIsoToRingEquiv.toMulEquiv).toAdditive

theorem coordinateUnitEquiv_naturality (m : U ⟶ V)
    (eU : U.left ≅ Spec R) (eV : V.left ≅ Spec S)
    (f : S ⟶ R) (h : eU.inv ≫ m.left = Spec.map f ≫ eV.inv)
    (s : (fullCoordinateUnitSheaf X).H' 0 V) :
    coordinateUnitEquiv eU (((fullCoordinateUnitSheaf X).cohomologyPresheaf 0).map m.op s) =
      Additive.ofMul (Units.map f.hom.toMonoidHom (coordinateUnitEquiv eV s).toMul) := by
  apply Additive.ext
  apply Units.ext
  change (sectionIso eU).hom.hom
      ((unitEquivZero U (((fullCoordinateUnitSheaf X).cohomologyPresheaf 0).map m.op s)).toMul :
        Γ(U.left, ⊤)) =
    f.hom ((sectionIso eV).hom.hom ((unitEquivZero V s).toMul : Γ(V.left, ⊤)))
  rw [unitEquivZero_natural]
  exact congrArg (fun k : Γ(V.left, ⊤) ⟶ R => k.hom ((unitEquivZero V s).toMul : Γ(V.left, ⊤)))
    (sectionIso_naturality m eU eV f h)

end

end ManuscriptAudit.EtaleAffineUnitNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleAffineUnitNaturality.sectionIso_naturality,
      ``ManuscriptAudit.EtaleAffineUnitNaturality.coordinateUnitEquiv_naturality] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
