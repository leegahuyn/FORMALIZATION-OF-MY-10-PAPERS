import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveSemilinear
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveUnits

/-! The actual semilinear projective map lies over the literal base field
map. Equality here is equality of scheme morphisms. -/

namespace ManuscriptAudit.WeierstrassProjectiveSemilinearBase

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassProjectiveSemilinear
open WeierstrassSemilinearAffineChart WeierstrassSemilinearCoordinate

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K L : Type u} [Field K] [Field L]
variable (W : WeierstrassCurve.Affine K) (e : K ≃+* L)

private theorem affineOpen_cancel_toSpec {R : Type u} [CommRing R]
    {f g : projectiveScheme W ⟶ Spec (CommRingCat.of R)}
    (h : affineOpen W ≫ f = affineOpen W ≫ g) : f = g := by
  let r := WeierstrassProjectiveUnits.restriction W
  letI : Mono r := ConcreteCategory.mono_of_injective r
    (WeierstrassProjectiveUnits.restriction_injective W)
  apply ext_to_Spec
  change (Scheme.ΓSpecIso _).inv ≫ f.appTop = (Scheme.ΓSpecIso _).inv ≫ g.appTop
  apply (cancel_mono r).mp
  have hh := congrArg (fun u : affineScheme W ⟶ Spec (CommRingCat.of R) =>
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ u.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of W.CoordinateRing)).hom) h
  simpa only [Scheme.Hom.comp_appTop, Category.assoc, r, WeierstrassProjectiveUnits.restriction] using hh

private abbrev V := W.map e.toRingHom

/-- The semilinear map of actual closures covers the actual spectrum
map of the chosen ground-field embedding. -/
theorem projectiveIso_base :
    (projectiveIso W e).hom ≫ toBase W =
      toBase (V W e) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) := by
  apply affineOpen_cancel_toSpec (V W e)
  let c := CommRingCat.ofHom (coordinateEquiv W e).toRingHom
  let a := CommRingCat.ofHom (algebraMap K W.CoordinateRing)
  let b := CommRingCat.ofHom (algebraMap L (V W e).CoordinateRing)
  let d := CommRingCat.ofHom e.toRingHom
  have h : a ≫ c = d ≫ b := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (coordinate_constant W e)
  calc
    _ = (affineOpen (V W e) ≫ (projectiveIso W e).hom) ≫ toBase W :=
      (Category.assoc _ _ _).symm
    _ = (affineSchemeIso W e).hom ≫ (affineOpen W ≫ toBase W) := by
      rw [affineOpen_projectiveIso, Category.assoc]
    _ = Spec.map (a ≫ c) := by
      rw [affineOpen_toBase, Spec.map_comp] <;> rfl
    _ = Spec.map (d ≫ b) := congrArg Spec.map h
    _ = (affineOpen (V W e) ≫ toBase (V W e)) ≫ Spec.map d := by
      rw [affineOpen_toBase, Spec.map_comp]
    _ = _ := Category.assoc _ _ _

end

end ManuscriptAudit.WeierstrassProjectiveSemilinearBase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveSemilinearBase.projectiveIso_base
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
