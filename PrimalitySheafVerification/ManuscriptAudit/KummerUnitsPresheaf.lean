import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.LocallySurjective
import PrimalitySheafVerification.ManuscriptAudit.KummerSiteCover

/-!
# Kummer local surjectivity on the affine étale site

The presheaf assigns the unit group of the coordinate ring to each affine
étale object. The power map is locally surjective wherever its degree is
invertible on every affine object.
-/

namespace ManuscriptAudit.KummerUnitsPresheaf

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable {X : Scheme.{u}}

/-- The coordinate ring of an object of the small affine étale site. -/
abbrev coordinateRing (U : X.AffineEtale) : CommRingCat.{u} := U.left.unop

/-- Units of the coordinate ring, with the group operation written additively. -/
def units (X : Scheme.{u}) : X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Additive (coordinateRing U.unop)ˣ)
  map f := AddCommGrpCat.ofHom (Units.map f.unop.left.unop.hom.toMonoidHom).toAdditive
  map_id _ := AddCommGrpCat.ext fun _ => Additive.ext (Units.ext rfl)
  map_comp _ _ := AddCommGrpCat.ext fun _ => Additive.ext (Units.ext rfl)

/-- Raise the units to the (d)-th power. -/
def power (X : Scheme.{u}) (d : ℕ) : units X ⟶ units X where
  app _ := AddCommGrpCat.ofHom (powMonoidHom d).toAdditive
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro a
    apply Additive.ext
    let m := Units.map f.unop.left.unop.hom.toMonoidHom
    change m a.toMul ^ d = m (a.toMul ^ d)
    exact (map_pow m a.toMul d).symm

/-- The power map on the coordinate-unit presheaf is locally surjective.
Its local preimage is the unit root on the finite étale root algebra. -/
theorem power_isLocallySurjective (d : ℕ) (hpos : 0 < d)
    (hd : ∀ U : X.AffineEtale, IsUnit (d : coordinateRing U)) :
    Presheaf.IsLocallySurjective (Scheme.AffineEtale.topology X) (power X d) where
  imageSieve_mem {U} s := by
    let A := coordinateRing U
    let a : Aˣ := (show Additive Aˣ from s).toMul
    let g : Spec A ⟶ X := U.hom
    letI : Etale g := U.prop
    let e := KummerSiteCover.rootMap d a
    letI : Etale e :=
      (KummerEtale.kummer_spec_finite_etale_cover hpos (hd U) a.isUnit).2.1
    let V : X.AffineEtale := Scheme.AffineEtale.mk (e ≫ g)
    let B := KummerSiteCover.rootAlgebra d a
    let f : V ⟶ U :=
      MorphismProperty.CostructuredArrow.homMk
        (CommRingCat.ofHom (algebraMap A B)).op trivial rfl
    let S : Sieve U := Sieve.ofArrows (fun _ : Unit => V) (fun _ => f)
    have hS : S ∈ Scheme.AffineEtale.topology X U := by
      rw [Scheme.AffineEtale.topology, Functor.mem_inducedTopology_iff_of_isCoverDense]
      change (Sieve.ofArrows (fun _ : Unit => V) (fun _ => f)).functorPushforward
        (Scheme.AffineEtale.Spec X) ∈ X.smallEtaleTopology (Scheme.AffineEtale.Spec X |>.obj U)
      rw [Sieve.functorPushforward_ofArrows]
      apply KummerSiteCover.singleton_mem_smallEtaleTopology
      change Function.Surjective e
      exact (KummerEtale.kummer_spec_finite_etale_cover hpos (hd U) a.isUnit).2.2.surj
    apply (Scheme.AffineEtale.topology X).superset_covering _ hS
    change Sieve.generate (Presieve.ofArrows (fun _ : Unit => V) (fun _ => f)) ≤ _
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro _
    rw [Presheaf.imageSieve_apply]
    obtain ⟨v, hv⟩ := KummerEtale.kummer_root_isUnit hpos a.isUnit
    refine ⟨Additive.ofMul v, ?_⟩
    apply Additive.ext
    apply Units.ext
    change (v : B) ^ d = algebraMap A B (a : A)
    rw [hv]
    exact KummerEtale.kummer_root_pow d (a : A)

/-- Over an affine base, invertibility of the degree pulls back to every
affine étale object. -/
theorem power_isLocallySurjective_spec (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) :
    Presheaf.IsLocallySurjective (Scheme.AffineEtale.topology (Spec R)) (power (Spec R) d) := by
  apply power_isLocallySurjective d hpos
  intro U
  let f : U.left ⟶ op R := Scheme.Spec.preimage U.hom
  simpa only [map_natCast] using hd.map f.unop.hom

end ManuscriptAudit.KummerUnitsPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerUnitsPresheaf.power_isLocallySurjective,
      ``ManuscriptAudit.KummerUnitsPresheaf.power_isLocallySurjective_spec] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
