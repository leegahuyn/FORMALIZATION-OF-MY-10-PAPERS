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

private theorem underlyingPoint_ker (x : (point A K).fiber.obj (algebraEtaleObject A B)) :
    (x.left (default : Spec (CommRingCat.of K))).asIdeal =
      RingHom.ker ((specOverHomEquiv A B K).symm x) := by
  let E := specOverHomEquiv A B K
  let f : B →ₐ[A] K := E.symm x
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) = x.left :=
    congrArg (fun g : Over.mk (specAlgebraMap A K) ⟶ Over.mk (specAlgebraMap A B) => g.left)
      (E.apply_symm_apply x)
  let o : Spec (CommRingCat.of K) := default
  letI : o.asIdeal.IsPrime := o.isPrime
  have ho : o.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  let b : CommRingCat.of B ⟶ CommRingCat.of K := CommRingCat.ofHom f.toRingHom
  have hb : (Spec.map b o).asIdeal = Ideal.comap b.hom o.asIdeal :=
    (congrArg PrimeSpectrum.asIdeal (Spec.map_apply b o)).trans
      (PrimeSpectrum.comap_asIdeal b.hom o)
  change (x.left o).asIdeal = RingHom.ker f
  rw [← hf]
  change (Spec.map b o).asIdeal = RingHom.ker f
  rw [hb, ho]
  exact (RingHom.ker_eq_comap_bot f).symm

/-- The prime indexing a geometric lift contracts to the actual underlying
point of that lift on the affine étale chart. -/
theorem rationalFiberEquiv_under (x : (point A K).fiber.obj (algebraEtaleObject A B)) :
    (rationalFiberEquiv A B K x).asIdeal.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B) =
      (x.left (default : Spec (CommRingCat.of K))).asIdeal := by
  rw [underlyingPoint_ker A B K]
  let f : B →ₐ[A] K := (specOverHomEquiv A B K).symm x
  let L := AlgHom.liftEquiv A K B K
  change (RingHom.ker (L f)).comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B) = RingHom.ker f
  calc
    _ = RingHom.ker (L.symm (L f)) := rfl
    _ = RingHom.ker f := congrArg (fun g : B →ₐ[A] K => RingHom.ker g) (L.symm_apply_apply f)

/-- Over a rational closed point, each underlying point of the affine étale
fiber has a unique geometric lift. -/
def rationalFiberEquivPreimage (hK : Function.Surjective (algebraMap A K)) :
    (point A K).fiber.obj (algebraEtaleObject A B) ≃
      (algebraEtaleObject A B).hom ⁻¹' {specAlgebraMap A K default} := by
  let q := Scheme.pointSmallEtaleFiberObjToPreimage (specAlgebraMap A K)
    (X := algebraEtaleObject A B) rfl
  apply Equiv.ofBijective q
  refine ⟨?_, Scheme.pointSmallEtaleFiberObjToPreimage_surjective
    (specAlgebraMap A K) rfl (algebraEtaleObject A B)⟩
  intro x y h
  let E := specOverHomEquiv A B K
  let f : B →ₐ[A] K := E.symm x
  let g : B →ₐ[A] K := E.symm y
  have hPoint : x.left (default : Spec (CommRingCat.of K)) =
      y.left (default : Spec (CommRingCat.of K)) := congrArg Subtype.val h
  have hKer : RingHom.ker f = RingHom.ker g := by
    rw [← underlyingPoint_ker A B K x, ← underlyingPoint_ker A B K y, hPoint]
  apply E.symm.injective
  apply AlgHom.ext
  intro b
  change f b = g b
  obtain ⟨a, ha⟩ := hK (f b)
  have hf : b - algebraMap A B a ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, f.commutes, ha, sub_self]
  have hg : b - algebraMap A B a ∈ RingHom.ker g := hKer ▸ hf
  rw [RingHom.mem_ker, map_sub, g.commutes, ha, sub_eq_zero] at hg
  exact hg.symm

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
      ``ManuscriptAudit.AffineEtaleRationalFiber.rationalFiberEquiv_under,
      ``ManuscriptAudit.AffineEtaleRationalFiber.rationalFiberEquivPreimage,
      ``ManuscriptAudit.AffineEtaleRationalFiber.skyscraperAffineIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
