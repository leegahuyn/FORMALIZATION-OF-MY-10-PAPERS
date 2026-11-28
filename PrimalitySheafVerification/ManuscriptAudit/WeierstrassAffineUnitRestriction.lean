import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleAffineUnitNaturality
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveUnits
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne

/-! Actual global units surject onto the actual affine chart units in
the degree-zero étale cohomology presheaf. -/

namespace ManuscriptAudit.WeierstrassAffineUnitRestriction

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure EtaleTwoOpenHOne
open EtaleCohomologyPresheafZero EtaleAffineUnitNaturality KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev F := fullCoordinateUnitSheaf (projectiveScheme W)
private abbrev A := CommRingCat.of W.CoordinateRing

/-- Every actual affine unit extends to the proper projective closure,
and this is the literal native cohomological restriction map. -/
theorem global_to_affine_surjective :
    Function.Surjective (((F W).cohomologyPresheaf 0).map (openArrow (affineOpen W)).op) := by
  let T := identityObject (projectiveScheme W)
  let U := Scheme.Etale.mk (affineOpen W)
  let e := unitEquivZero T
  let eU : U.left ≅ Spec (A W) := Iso.refl _
  let E := coordinateUnitEquiv eU
  intro c
  obtain ⟨a, ha⟩ := (WeierstrassAffineUnits.unitsEquiv W).surjective (E c).toMul
  let v := Units.map (WeierstrassProjectiveUnits.scalarMap W).hom.toMonoidHom a
  let x := e.symm (Additive.ofMul v)
  refine ⟨x, E.injective ?_⟩
  apply Additive.ext
  apply Units.ext
  change (sectionIso eU).hom.hom
    ((unitEquivZero U (((F W).cohomologyPresheaf 0).map (openArrow (affineOpen W)).op x)).toMul :
      Γ(U.left, ⊤)) = ((E c).toMul : W.CoordinateRing)
  have hSec : (sectionIso eU).hom = (Scheme.ΓSpecIso (A W)).hom := by
    change (𝟙 (Spec (A W))).appTop ≫ (Scheme.ΓSpecIso (A W)).hom = _
    rw [Scheme.Hom.id_appTop, Category.id_comp]
  rw [hSec, unitEquivZero_natural]
  have he : unitEquivZero T x = Additive.ofMul v := e.apply_symm_apply _
  rw [he]
  change (WeierstrassProjectiveUnits.restriction W).hom
    ((WeierstrassProjectiveUnits.scalarMap W).hom (a : K)) =
      ((E c).toMul : W.CoordinateRing)
  have h₁ := congrArg (fun f : CommRingCat.of K ⟶ A W => f.hom (a : K))
    (WeierstrassProjectiveUnits.scalarMap_restriction W)
  exact h₁.trans ((WeierstrassAffineUnits.unitsEquiv_apply_val W a).symm.trans
    (congrArg Units.val ha))

end

end ManuscriptAudit.WeierstrassAffineUnitRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.WeierstrassAffineUnitRestriction.global_to_affine_surjective
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
