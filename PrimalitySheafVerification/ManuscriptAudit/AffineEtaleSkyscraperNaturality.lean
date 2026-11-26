import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSkyscraperIndexNaturality

/-!
# Restriction of rational-skyscraper sections on integral affine charts

The actual skyscraper restriction is pullback of the product
coordinates along the contraction of height-one prime ideals.
-/

namespace ManuscriptAudit.AffineEtaleClosedPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GenericEtaleUnitSections IsDedekindDomain

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A B C : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower A B C] [Algebra.Etale A B] [Algebra.Etale A C] [Algebra.Etale B C]

/-- Contraction on the two height-one fibers over a fixed base point. -/
def contractFiber (p : HeightOneSpectrum A) (q : {q : HeightOneSpectrum C // comap A C q = p}) :
    {q : HeightOneSpectrum B // comap A B q = p} :=
  ⟨comap B C q.val, (show comap A B (comap B C q.val) = comap A C q.val from by
    apply HeightOneSpectrum.ext
    change (q.val.asIdeal.comap (algebraMap B C)).comap (algebraMap A B) =
      q.val.asIdeal.comap (algebraMap A C)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A B C]).trans q.property⟩

variable (K : Type) [Field K] [IsAlgClosed K] [Algebra A K]

private abbrev s := Spec.map (CommRingCat.ofHom (algebraMap A K))

set_option maxHeartbeats 1000000 in
/-- The product coordinates of the actual rational skyscraper restrict
by contraction of height-one points. -/
theorem rationalSkyscraperHeightOneIso_naturality (p : HeightOneSpectrum A)
    (hs : (s A K (default : Spec (CommRingCat.of K))).asIdeal = p.asIdeal)
    (hK : Function.Surjective (algebraMap A K)) (M : AddCommGrpCat.{0}) :
    ((AffineEtaleRationalFiber.point A K).skyscraperSheaf M).obj.map
        (algebraEtaleMap (IsScalarTower.toAlgHom A B C)).op ≫
      (rationalSkyscraperHeightOneIso A C K p hs hK M).hom =
    (rationalSkyscraperHeightOneIso A B K p hs hK M).hom ≫
      Pi.map' (contractFiber A B C p) (fun _ ↦ 𝟙 M) := by
  let Φ := AffineEtaleRationalFiber.point A K
  let f := algebraEtaleMap (IsScalarTower.toAlgHom A B C)
  let e := heightOneIndexEquiv A K p hs hK B
  let e' := heightOneIndexEquiv A K p hs hK C
  have h (q : {q : HeightOneSpectrum C // comap A C q = p}) :
      Φ.fiber.map f (e'.symm q) = e.symm (contractFiber A B C p q) := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change (e (Φ.fiber.map f (e'.symm q))).val = comap B C q.val
    have r := heightOneIndexEquiv_map A K p hs hK B C (e'.symm q)
    change (e (Φ.fiber.map f (e'.symm q))).val = comap B C (e' (e'.symm q)).val at r
    simpa only [Equiv.apply_symm_apply] using r
  let liftB := fun _ : Φ.fiber.obj (algebraEtaleObject A B) ↦ M
  let liftC := fun _ : Φ.fiber.obj (algebraEtaleObject A C) ↦ M
  let pointB := fun _ : {q : HeightOneSpectrum B // comap A B q = p} ↦ M
  let pointC := fun _ : {q : HeightOneSpectrum C // comap A C q = p} ↦ M
  change Pi.map' (f := liftB) (g := liftC) (Φ.fiber.map f) (fun _ ↦ 𝟙 M) ≫
      (Pi.whiskerEquiv (f := liftC) (g := pointC) e' (fun _ ↦ Iso.refl M)).hom =
    (Pi.whiskerEquiv (f := liftB) (g := pointB) e (fun _ ↦ Iso.refl M)).hom ≫
      Pi.map' (f := pointB) (g := pointC) (contractFiber A B C p) (fun _ ↦ 𝟙 M)
  apply Pi.hom_ext
  intro q
  simp only [Category.assoc, Pi.whiskerEquiv_hom, Pi.map'_comp_π, Pi.map'_comp_π_assoc,
    Iso.refl_inv, eqToHom_refl, Category.id_comp, Category.comp_id, h]

end

end ManuscriptAudit.AffineEtaleClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineEtaleClosedPoints.rationalSkyscraperHeightOneIso_naturality
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
