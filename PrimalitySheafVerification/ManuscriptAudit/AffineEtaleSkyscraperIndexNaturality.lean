import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleClosedFiberSkyscraper
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitNaturality

/-!
# Restriction of the rational-skyscraper indices

A geometric lift to a chart is labeled by its actual height-one
prime. Postcomposing that lift with a map of integral affine étale
charts contracts the prime along the corresponding algebra map.
-/

namespace ManuscriptAudit.AffineEtaleClosedPoints

open AlgebraicGeometry CategoryTheory Opposite
open GenericEtaleUnitSections IsDedekindDomain

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsDomain A]
variable (K : Type) [Field K] [IsAlgClosed K] [Algebra A K]

private abbrev s := Spec.map (CommRingCat.ofHom (algebraMap A K))
private abbrev zeroPoint : Spec (CommRingCat.of K) := default

variable (p : HeightOneSpectrum A)
variable (hs : (s A K (zeroPoint K)).asIdeal = p.asIdeal)
variable (hK : Function.Surjective (algebraMap A K))

private abbrev changeFiber {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B] :
    (algebraEtaleObject A B).hom ⁻¹' {s A K (zeroPoint K)} ≃
      (algebraEtaleObject A B).hom ⁻¹' {⟨p.asIdeal, p.isPrime⟩} :=
  Equiv.setCongr (congrArg (fun x ↦ (algebraEtaleObject A B).hom ⁻¹' {x}) (PrimeSpectrum.ext hs))

variable (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra.Etale A B]

/-- The actual indices of a rational skyscraper on the chart, given as
height-one primes lying over the chosen rational closed point. -/
def heightOneIndexEquiv :
    (AffineEtaleRationalFiber.point A K).fiber.obj (algebraEtaleObject A B) ≃
      {q : HeightOneSpectrum B // comap A B q = p} :=
  (AffineEtaleRationalFiber.rationalFiberEquivPreimage A B K hK).trans
    ((changeFiber A K p hs).trans (preimageHeightOneEquiv A B p))

/-- The selected index is the actual underlying prime of the geometric lift. -/
theorem heightOneIndexEquiv_asIdeal
    (t : (AffineEtaleRationalFiber.point A K).fiber.obj (algebraEtaleObject A B)) :
    (heightOneIndexEquiv A K p hs hK B t).val.asIdeal = (t.left (zeroPoint K)).asIdeal := by
  let e := AffineEtaleRationalFiber.rationalFiberEquivPreimage A B K hK
  change ((changeFiber A K p hs) (e t)).val.asIdeal = (t.left (zeroPoint K)).asIdeal
  simp only [changeFiber, Equiv.setCongr_apply]
  rfl

variable (C : Type) [CommRing C] [IsDomain C] [Algebra A C] [Algebra.Etale A C]
  [Algebra B C] [IsScalarTower A B C] [Algebra.Etale B C]

/-- Under the actual fiber functor, postcomposition of a rational lift
corresponds to contraction of its height-one prime. -/
theorem heightOneIndexEquiv_map
    (t : (AffineEtaleRationalFiber.point A K).fiber.obj (algebraEtaleObject A C)) :
    (heightOneIndexEquiv A K p hs hK B
      ((AffineEtaleRationalFiber.point A K).fiber.map
        (algebraEtaleMap (IsScalarTower.toAlgHom A B C)) t)).val =
      comap B C (heightOneIndexEquiv A K p hs hK C t).val := by
  apply HeightOneSpectrum.ext
  rw [heightOneIndexEquiv_asIdeal]
  change ((t.left ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (zeroPoint K)).asIdeal =
    ((heightOneIndexEquiv A K p hs hK C t).val.asIdeal).comap (algebraMap B C)
  rw [heightOneIndexEquiv_asIdeal]
  let x : Spec (CommRingCat.of C) := t.left (zeroPoint K)
  let f : CommRingCat.of B ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap B C)
  change (Spec.map f x).asIdeal = Ideal.comap f.hom x.asIdeal
  exact (congrArg PrimeSpectrum.asIdeal (Spec.map_apply f x)).trans
    (PrimeSpectrum.comap_asIdeal f.hom x)

end

end ManuscriptAudit.AffineEtaleClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleClosedPoints.heightOneIndexEquiv_asIdeal,
      ``ManuscriptAudit.AffineEtaleClosedPoints.heightOneIndexEquiv_map] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
