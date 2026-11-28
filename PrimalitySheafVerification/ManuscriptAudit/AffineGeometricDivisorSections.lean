import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorSheaf
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleClosedFiberSkyscraper
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorByBasePoint

/-! The sections of the true finite-support divisor sheaf on an integral
affine étale chart are precisely its finite cycles of height one. -/

namespace ManuscriptAudit.AffineGeometricDivisorSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain GenericEtaleUnitSections AffineEtaleClosedPoints AffineGeometricDivisorSheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false

private def productAddEquiv {I : Type} (M : AddCommGrpCat.{0}) :
    ↥(∏ᶜ (fun _ : I ↦ M) : AddCommGrpCat.{0}) ≃+ (I → ↥M) where
  __ := Concrete.productEquiv (fun _ : I ↦ M)
  map_add' x y := by
    funext i
    let e := Concrete.productEquiv (fun _ : I ↦ M)
    change e (x + y) i = e x i + e y i
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply,
      Concrete.productEquiv_apply_apply]
    exact (Pi.π (fun _ : I ↦ M) i).hom.map_add x y

variable (K A B : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.Etale A B]

/-- The true object on the affine basis of the small étale site. -/
def chartObject : (X A).AffineEtale := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  letI : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B))
  exact Scheme.AffineEtale.mk f

/-- The coefficient in one geometric skyscraper is a function on the actual
fiber of the map of height-one spectra. -/
def chartComponentEquiv (p : HeightOneSpectrum A) :
    (skyscraper K A p).obj.obj (op (algebraEtaleObject A B)) ≃+
      ({q : HeightOneSpectrum B // comap A B q = p} → ℤ) := by
  let g := pointAlgHom K A p
  letI : Algebra A K := g.toRingHom.toAlgebra
  have hs : (Spec.map (CommRingCat.ofHom (algebraMap A K))
      (default : Spec (CommRingCat.of K))).asIdeal = p.asIdeal := by
    exact congrArg PrimeSpectrum.asIdeal (pointMap_default K A p)
  have hK : Function.Surjective (algebraMap A K) := by
    intro c
    exact ⟨algebraMap K A c, g.commutes c⟩
  let e := rationalSkyscraperHeightOneIso A B K p hs hK (AddCommGrpCat.of ℤ)
  exact e.addCommGroupIsoToAddEquiv.trans (productAddEquiv (AddCommGrpCat.of ℤ))

set_option maxHeartbeats 1000000 in
/-- The actual global section of the native divisor sheaf on an integral
étale chart is a finite-support integer cycle on its height-one spectrum. -/
def chartSectionsEquiv :
    (affineDivisorSheaf K A).obj.obj (op (chartObject A B)) ≃+
      (HeightOneSpectrum B →₀ ℤ) := by
  change (Π₀ p : HeightOneSpectrum A, (skyscraper K A p).obj.obj (op (algebraEtaleObject A B))) ≃+ _
  exact (DFinsupp.mapRange.addEquiv (chartComponentEquiv K A B)).trans
    (cyclesByBasePoint A B).symm

end

end ManuscriptAudit.AffineGeometricDivisorSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineGeometricDivisorSections.chartSectionsEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
