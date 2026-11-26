import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.RingTheory.Etale.Field
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections
import PrimalitySheafVerification.ManuscriptAudit.IntegralRationalPoints

/-!
# Actual rational-point skyscraper sections on affine étale charts

The fiber of the geometric point on an affine étale object is the set
of rational lifts. These are exactly the prime ideals of the actual
tensor-product fiber. Thus the skyscraper sections are the product of the
coefficient groups indexed by those primes.
-/

namespace ManuscriptAudit.AffineEtaleRationalFiber

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GenericEtaleUnitSections
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

private abbrev specAlgebraMap (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

private def specOverHomEquiv (A B K : Type) [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] :
    (B →ₐ[A] K) ≃
      (Over.mk (specAlgebraMap A K) ⟶ Over.mk (specAlgebraMap A B)) where
  toFun f := Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specAlgebraMap A B = specAlgebraMap A K
    simp only [specAlgebraMap, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact f.commutes)
  invFun g :=
    { (Spec.preimage g.left).hom with
      commutes' := fun r => by
        have h : CommRingCat.ofHom (algebraMap A B) ≫ Spec.preimage g.left =
            CommRingCat.ofHom (algebraMap A K) := by
          have hg : g.left ≫ specAlgebraMap A B = specAlgebraMap A K := Over.w g
          simpa only [specAlgebraMap, Spec.preimage_comp, Spec.preimage_map] using
            congrArg Spec.preimage hg
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) r }
  left_inv f := by
    apply AlgHom.ext
    intro x
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom x = f x
    rw [Spec.preimage_map]
    rfl
  right_inv g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Spec.preimage g.left).hom) = g.left
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]

variable (A B K : Type) [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
  [Algebra A B] [Algebra A K] [Algebra.Etale A B]

/-- The geometric point of the given ring map from the base to the field. -/
abbrev point : (Spec (CommRingCat.of A)).smallEtaleTopology.Point :=
  Scheme.pointSmallEtale (specAlgebraMap A K)

/-- Every point in the actual geometric fiber of the affine chart has
a unique prime in the tensor-product coordinate ring. -/
def rationalFiberEquiv :
    (point A K).fiber.obj (algebraEtaleObject A B) ≃ PrimeSpectrum (K ⊗[A] B) := by
  haveI : Module.Finite K (K ⊗[A] B) :=
    Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)
  haveI : Algebra.IsIntegral K (K ⊗[A] B) :=
    ⟨fun x ↦ isIntegral_of_noetherian (IsNoetherian.iff_fg.2 inferInstance) x⟩
  change (Over.mk (specAlgebraMap A K) ⟶ Over.mk (specAlgebraMap A B)) ≃ _
  exact (specOverHomEquiv A B K).symm.trans
    ((AlgHom.liftEquiv A K B K).trans
      (IntegralRationalPoints.primeSpectrumEquivAlgHom K (K ⊗[A] B)).symm)

/-- The sections of the actual étale skyscraper are indexed by the
prime ideals of the scheme-theoretic affine fiber. -/
def skyscraperAffineIso (M : AddCommGrpCat.{0}) :
    ((point A K).skyscraperSheaf M).obj.obj (op (algebraEtaleObject A B)) ≅
      ∏ᶜ (fun _ : PrimeSpectrum (K ⊗[A] B) ↦ M) := by
  change (∏ᶜ (fun _ : (point A K).fiber.obj (algebraEtaleObject A B) ↦ M)) ≅ _
  exact Pi.whiskerEquiv (rationalFiberEquiv A B K) (fun _ ↦ Iso.refl M)

end

end ManuscriptAudit.AffineEtaleRationalFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleRationalFiber.rationalFiberEquiv,
      ``ManuscriptAudit.AffineEtaleRationalFiber.skyscraperAffineIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
