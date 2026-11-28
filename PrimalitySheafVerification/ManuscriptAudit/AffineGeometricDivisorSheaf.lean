import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleSheaf

/-! The actual divisor sheaf of an affine geometric Dedekind curve is
the finite-support family of the integer skyscrapers at its closed points. -/

namespace ManuscriptAudit.AffineGeometricDivisorSheaf

open AlgebraicGeometry CategoryTheory IsDedekindDomain

noncomputable section

variable (K A : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A]

abbrev X := Spec (CommRingCat.of A)

/-- A geometric closed point has actual residue field equal to the
algebraically closed ground field. -/
def residueEquiv (p : HeightOneSpectrum A) : K ≃ₐ[K] A ⧸ p.asIdeal := by
  letI : p.asIdeal.IsMaximal := p.isMaximal
  letI : Field (A ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  letI : Module.Finite K (A ⧸ p.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing K (A ⧸ p.asIdeal)
  exact AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ p.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The actual coordinate reduction at a geometric closed point. -/
def pointAlgHom (p : HeightOneSpectrum A) : A →ₐ[K] K :=
  (residueEquiv K A p).symm.toAlgHom.comp (Ideal.Quotient.mkₐ K p.asIdeal)

theorem point_ker (p : HeightOneSpectrum A) :
    RingHom.ker (pointAlgHom K A p).toRingHom = p.asIdeal := by
  ext a
  change (residueEquiv K A p).symm (Ideal.Quotient.mk p.asIdeal a) = 0 ↔ a ∈ p.asIdeal
  constructor
  · intro ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (residueEquiv K A p).symm.injective
    exact ha.trans (map_zero _).symm
  · intro ha
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- The geometric morphism with center the actual height-one point. -/
def pointMap (p : HeightOneSpectrum A) : Spec (CommRingCat.of K) ⟶ X A :=
  Spec.map (CommRingCat.ofHom (pointAlgHom K A p).toRingHom)

theorem pointMap_default (p : HeightOneSpectrum A) :
    pointMap K A p (default : Spec (CommRingCat.of K)) =
      (⟨p.asIdeal, p.isPrime⟩ : PrimeSpectrum A) := by
  apply PrimeSpectrum.ext
  let x : Spec (CommRingCat.of K) := default
  letI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  let f : CommRingCat.of A ⟶ CommRingCat.of K := CommRingCat.ofHom (pointAlgHom K A p).toRingHom
  change (Spec.map f x).asIdeal = p.asIdeal
  calc
    _ = Ideal.comap f.hom x.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal (Spec.map_apply f x)).trans
        (PrimeSpectrum.comap_asIdeal f.hom x)
    _ = p.asIdeal := by
      rw [hx, ← RingHom.ker_eq_comap_bot]
      exact point_ker K A p

private abbrev comparison := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}

/-- The integer skyscraper sheaf at the actual geometric point. -/
abbrev skyscraper (p : HeightOneSpectrum A) : Sheaf (X A).smallEtaleTopology AddCommGrpCat.{0} :=
  (Scheme.pointSmallEtale (pointMap K A p)).skyscraperSheaf (AddCommGrpCat.of ℤ)

/-- The native divisor sheaf on the literal affine étale basis. -/
def affineDivisorSheaf : Sheaf (Scheme.AffineEtale.topology (X A)) AddCommGrpCat.{0} :=
  FiniteSupportPresheaf.affineEtaleDirectSum (X A)
    (fun p : HeightOneSpectrum A => (comparison A).inverse.obj (skyscraper K A p))

/-- The same actual divisor sheaf on the full small étale site. -/
def divisorSheaf : Sheaf (X A).smallEtaleTopology AddCommGrpCat.{0} :=
  (comparison A).functor.obj (affineDivisorSheaf K A)

def restrictionIso : (comparison A).inverse.obj (divisorSheaf K A) ≅ affineDivisorSheaf K A :=
  ((comparison A).unitIso.app (affineDivisorSheaf K A)).symm

end

end ManuscriptAudit.AffineGeometricDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricDivisorSheaf.pointMap_default,
      ``ManuscriptAudit.AffineGeometricDivisorSheaf.affineDivisorSheaf,
      ``ManuscriptAudit.AffineGeometricDivisorSheaf.divisorSheaf] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
