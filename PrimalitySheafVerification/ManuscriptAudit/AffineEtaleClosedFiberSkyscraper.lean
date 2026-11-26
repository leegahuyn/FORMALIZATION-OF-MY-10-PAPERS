import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleClosedPoints
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRationalFiber

/-!
# Indexing a rational skyscraper by affine chart divisors

The points above a rational closed point are exactly the height-one
primes lying over its prime. This identifies the coordinates of the
actual geometric skyscraper with the corresponding divisor coordinates.
-/

namespace ManuscriptAudit.AffineEtaleClosedPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GenericEtaleUnitSections IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra.Etale A B]

private theorem algebraMap_injective : Function.Injective (algebraMap A B) := by
  apply (injective_iff_map_eq_zero (algebraMap A B)).2
  intro a ha
  by_contra hn
  have hr : IsRegular a := isRegular_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
  have hm := Module.Flat.isSMulRegular_of_isRegular (M := B) hr
  have he : a • (1 : B) = a • (0 : B) := by
    rw [← Algebra.algebraMap_eq_smul_one, ha, smul_zero]
  exact one_ne_zero (hm he)

private theorem specChart_asIdeal (x : Spec (CommRingCat.of B)) :
    ((algebraEtaleObject A B).hom x).asIdeal = x.asIdeal.comap (algebraMap A B) := by
  let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  change (Spec.map f x).asIdeal = _
  exact (congrArg PrimeSpectrum.asIdeal (Spec.map_apply f x)).trans
    (PrimeSpectrum.comap_asIdeal f.hom x)

/-- The actual topological fiber over a height-one base point consists of
the height-one primes whose contraction is that point. -/
def preimageHeightOneEquiv (p : HeightOneSpectrum A) :
    (algebraEtaleObject A B).hom ⁻¹' {⟨p.asIdeal, p.isPrime⟩} ≃
      {q : HeightOneSpectrum B // comap A B q = p} where
  toFun x := by
    have h := congrArg PrimeSpectrum.asIdeal x.property
    have hc : x.val.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      (specChart_asIdeal A B x.val).symm.trans h
    have hNonzero : x.val.asIdeal ≠ ⊥ := by
      intro hx
      have hk : RingHom.ker (algebraMap A B) = ⊥ := by
        ext r
        rw [RingHom.mem_ker, Ideal.mem_bot, ← map_zero (algebraMap A B)]
        exact (algebraMap_injective A B).eq_iff
      rw [hx, ← RingHom.ker_eq_comap_bot, hk] at hc
      exact p.ne_bot hc.symm
    exact ⟨⟨x.val.asIdeal, x.val.isPrime, hNonzero⟩, HeightOneSpectrum.ext hc⟩
  invFun q := by
    let x : Spec (CommRingCat.of B) := ⟨q.val.asIdeal, q.val.isPrime⟩
    have hc : x.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal q.property
    exact ⟨x, PrimeSpectrum.ext ((specChart_asIdeal A B x).trans hc)⟩
  left_inv x := Subtype.ext (PrimeSpectrum.ext rfl)
  right_inv q := Subtype.ext (HeightOneSpectrum.ext rfl)

variable (K : Type) [Field K] [IsAlgClosed K] [Algebra A K]

private abbrev s := Spec.map (CommRingCat.ofHom (algebraMap A K))

/-- On the affine chart, the actual rational skyscraper is the product
over the height-one divisor coordinates over the chosen closed point. -/
def rationalSkyscraperHeightOneIso (p : HeightOneSpectrum A)
    (hs : (s A K (default : Spec (CommRingCat.of K))).asIdeal = p.asIdeal)
    (hK : Function.Surjective (algebraMap A K)) (M : AddCommGrpCat.{0}) :
    ((AffineEtaleRationalFiber.point A K).skyscraperSheaf M).obj.obj
        (op (algebraEtaleObject A B)) ≅
      ∏ᶜ (fun _ : {q : HeightOneSpectrum B // comap A B q = p} ↦ M) := by
  let z : Spec (CommRingCat.of A) := ⟨p.asIdeal, p.isPrime⟩
  have hz : s A K (default : Spec (CommRingCat.of K)) = z := PrimeSpectrum.ext hs
  let e := AffineEtaleRationalFiber.rationalFiberEquivPreimage A B K hK
  let e' : (algebraEtaleObject A B).hom ⁻¹' {s A K (default : Spec (CommRingCat.of K))} ≃
      (algebraEtaleObject A B).hom ⁻¹' {z} :=
    Equiv.setCongr (congrArg (fun x ↦ (algebraEtaleObject A B).hom ⁻¹' {x}) hz)
  change (∏ᶜ (fun _ : (AffineEtaleRationalFiber.point A K).fiber.obj (algebraEtaleObject A B) ↦ M)) ≅ _
  exact Pi.whiskerEquiv (e.trans (e'.trans (preimageHeightOneEquiv A B p))) (fun _ ↦ Iso.refl M)

end

end ManuscriptAudit.AffineEtaleClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleClosedPoints.preimageHeightOneEquiv,
      ``ManuscriptAudit.AffineEtaleClosedPoints.rationalSkyscraperHeightOneIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
