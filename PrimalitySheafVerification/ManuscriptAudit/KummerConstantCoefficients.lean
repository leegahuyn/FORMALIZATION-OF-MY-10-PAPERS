import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.KummerRootLabels
import PrimalitySheafVerification.ManuscriptAudit.KummerUnitsPresheaf

/-!
# Constant coefficients for the affine étale roots-of-unity presheaf

Over an algebraically closed coefficient field, the constant-to-roots
presheaf morphism is locally bijective for an invertible positive degree.
The affine étale covers used in the proof localize at the clopen fiber
idempotents of each root label.
-/

namespace ManuscriptAudit.KummerConstantCoefficients

open AlgebraicGeometry CategoryTheory Opposite
open KummerRootLabels KummerUnitsPresheaf

universe u

noncomputable section

/-- Actual ring roots of unity on affine étale objects, viewed additively. -/
def roots (X : Scheme.{u}) (d : ℕ) : X.AffineEtaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Additive (rootsOfUnity d (coordinateRing U.unop)))
  map f := AddCommGrpCat.ofHom (mapRoots d f.unop.left.unop.hom).toAdditive
  map_id _ := AddCommGrpCat.ext fun _ => Additive.ext (Subtype.ext (Units.ext rfl))
  map_comp _ _ := AddCommGrpCat.ext fun _ => Additive.ext (Subtype.ext (Units.ext rfl))

variable {K : Type u} [Field K] (R : CommRingCat.{u}) [Algebra K R]

private def baseMap (U : (Spec R).AffineEtale) : R →+* coordinateRing U :=
  (AlgebraicGeometry.Spec.preimage U.hom).hom

private def coefficientMap (U : (Spec R).AffineEtale) : K →+* coordinateRing U :=
  (baseMap R U).comp (algebraMap K R)

private theorem coefficientMap_natural {U V : (Spec R).AffineEtale} (f : U ⟶ V) :
    f.left.unop.hom.comp (coefficientMap (K := K) R V) = coefficientMap R U := by
  have hw : AlgebraicGeometry.Spec.map f.left.unop ≫ V.hom = U.hom := by
    simpa using f.w
  have h := congrArg (fun g : Spec (coordinateRing U) ⟶ Spec R =>
      (AlgebraicGeometry.Spec.preimage g).hom) hw
  rw [AlgebraicGeometry.Spec.preimage_comp, AlgebraicGeometry.Spec.preimage_map,
    CommRingCat.hom_comp] at h
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun h (algebraMap K R x)

/-- The constant ring roots, written additively. -/
abbrev coefficientGroup (K : Type u) [Field K] (d : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Additive (rootsOfUnity d K))

/-- The canonical map from constant coefficient roots to affine root sections. -/
def constantToRoots (d : ℕ) :
    (Functor.const ((Spec R).AffineEtaleᵒᵖ)).obj (coefficientGroup K d) ⟶ roots (Spec R) d where
  app U := AddCommGrpCat.ofHom (mapRoots d (coefficientMap R U.unop)).toAdditive
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro a
    apply Additive.ext
    apply Subtype.ext
    apply Units.ext
    exact (DFunLike.congr_fun (coefficientMap_natural (K := K) R f.unop)
      ((a.toMul : Kˣ) : K)).symm

private theorem affine_family_cover_iff {X : Scheme.{u}} {U : X.AffineEtale}
    {ι : Type*} {V : ι → X.AffineEtale} (f : ∀ i, V i ⟶ U) :
    Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology X U ↔
      ⋃ i, Set.range (Scheme.Spec.map (f i).left) = Set.univ := by
  rw [Scheme.AffineEtale.topology, Functor.mem_inducedTopology_iff_of_isCoverDense,
    Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff] <;> rfl

/-- The constant-root map is locally injective, including at the empty affine
scheme, where the empty family covers. -/
theorem constantToRoots_locallyInjective (d : ℕ) :
    Presheaf.IsLocallyInjective (Scheme.AffineEtale.topology (Spec R))
      (constantToRoots (K := K) R d) where
  equalizerSieve_mem {U} x y h := by
    let A := coordinateRing U.unop
    rcases subsingleton_or_nontrivial A with hA | hA
    · letI : Subsingleton A := hA
      let f : ∀ _ : Empty, U.unop ⟶ U.unop := fun _ => 𝟙 U.unop
      have hc : Sieve.ofArrows (fun _ : Empty => U.unop) f ∈
          Scheme.AffineEtale.topology (Spec R) U.unop := by
        rw [affine_family_cover_iff]
        apply Set.eq_univ_of_forall
        intro P
        change PrimeSpectrum A at P
        exact isEmptyElim P
      apply (Scheme.AffineEtale.topology (Spec R)).superset_covering _ hc
      change Sieve.generate (Presieve.ofArrows (fun _ : Empty => U.unop) f) ≤ _
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro i
      exact isEmptyElim i
    · letI : Nontrivial A := hA
      have hxy : x = y := by
        apply Additive.ext
        apply rootsOfUnity.coe_injective
        apply (coefficientMap (K := K) R U.unop).injective
        exact congrArg (fun a : Additive (rootsOfUnity d A) => ((a.toMul : Aˣ) : A)) h
      rw [hxy, Presheaf.equalizerSieve_self_eq_top]
      exact (Scheme.AffineEtale.topology (Spec R)).top_mem _

variable [IsAlgClosed K] {d : ℕ} [NeZero d] [NeZero (d : K)]

/-- Each root section is the image of a constant coefficient root locally.
The actual covers are the affine opens cut out by the fiber idempotents. -/
theorem constantToRoots_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.AffineEtale.topology (Spec R))
      (constantToRoots (K := K) R d) where
  imageSieve_mem {U} s := by
    let A := coordinateRing U
    letI : Algebra K A := (coefficientMap (K := K) R U).toAlgebra
    let a : rootsOfUnity d A := (show Additive (rootsOfUnity d A) from s).toMul
    choose e _he hFiber using fun ζ : rootsOfUnity d K =>
      locallyConstantRootTag_idempotent a ζ
    let B := fun ζ => Localization.Away (e ζ)
    let r : ∀ ζ, A →+* B ζ := fun ζ => algebraMap A (B ζ)
    let eMap : ∀ ζ, Spec (CommRingCat.of (B ζ)) ⟶ Spec A :=
      fun ζ => AlgebraicGeometry.Spec.map (CommRingCat.ofHom (r ζ))
    let g : Spec A ⟶ Spec R := U.hom
    letI : Etale g := U.prop
    let V : rootsOfUnity d K → (Spec R).AffineEtale := fun ζ => by
      letI : IsOpenImmersion (eMap ζ) :=
        Scheme.isOpenImmersion_SpecMap_localizationAway (R := A) (e ζ)
      exact Scheme.AffineEtale.mk (eMap ζ ≫ g)
    let f : ∀ ζ, V ζ ⟶ U := fun ζ =>
      MorphismProperty.CostructuredArrow.homMk (CommRingCat.ofHom (r ζ)).op trivial rfl
    have hRange (ζ : rootsOfUnity d K) :
        Set.range (PrimeSpectrum.comap (r ζ)) = PrimeSpectrum.basicOpen (e ζ) :=
      PrimeSpectrum.localization_away_comap_range (B ζ) (e ζ)
    have hc : Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology (Spec R) U := by
      apply (affine_family_cover_iff f).mpr
      change ⋃ ζ, Set.range (PrimeSpectrum.comap (r ζ)) = Set.univ
      apply Set.eq_univ_of_forall
      intro P
      let ζ := locallyConstantRootTag (K := K) a P
      have hP : P ∈ (PrimeSpectrum.basicOpen (e ζ) : Set (PrimeSpectrum A)) := by
        rw [← hFiber ζ] <;> rfl
      rw [← hRange ζ] at hP
      exact Set.mem_iUnion.mpr ⟨ζ, hP⟩
    apply (Scheme.AffineEtale.topology (Spec R)).superset_covering _ hc
    change Sieve.generate (Presieve.ofArrows V f) ≤ _
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro ζ
    rw [Presheaf.imageSieve_apply]
    refine ⟨Additive.ofMul ζ, ?_⟩
    apply Additive.ext
    change mapRoots d (coefficientMap R (V ζ)) ζ = mapRoots d (r ζ) a
    letI : Algebra K (B ζ) := (coefficientMap (K := K) R (V ζ)).toAlgebra
    let alg : A →ₐ[K] B ζ :=
      { toRingHom := r ζ
        commutes' x := DFunLike.congr_fun (coefficientMap_natural (K := K) R (f ζ)) x }
    change mapRoots d (algebraMap K (B ζ)) ζ = mapRoots d alg.toRingHom a
    apply locallyConstantRootTag_injective (K := K)
    apply LocallyConstant.ext
    intro Q
    rw [locallyConstantRootTag_coeff, locallyConstantRootTag_natural]
    have hQ : PrimeSpectrum.comap (r ζ) Q ∈
        (PrimeSpectrum.basicOpen (e ζ) : Set (PrimeSpectrum A)) := by
      rw [← hRange ζ]
      exact ⟨Q, rfl⟩
    rw [← hFiber ζ] at hQ
    change locallyConstantRootTag (K := K) a (PrimeSpectrum.comap (r ζ) Q) = ζ at hQ
    exact hQ.symm

/-- The sheafification of the affine root presheaf is the actual constant
sheaf associated to the coefficient roots. -/
def constantRootSheafIso :
    (constantSheaf (Scheme.AffineEtale.topology (Spec R)) AddCommGrpCat.{u}).obj
        (coefficientGroup K d) ≅
      (presheafToSheaf (Scheme.AffineEtale.topology (Spec R)) AddCommGrpCat.{u}).obj
        (roots (Spec R) d) := by
  let J := Scheme.AffineEtale.topology (Spec R)
  let η := constantToRoots (K := K) R d
  have hW : J.W η := (J.W_iff_isLocallyBijective η).mpr
    ⟨constantToRoots_locallyInjective (K := K) R d,
      constantToRoots_locallySurjective (K := K) (d := d) R⟩
  letI : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map η) := (J.W_iff η).mp hW
  exact asIso ((presheafToSheaf J AddCommGrpCat.{u}).map η)

end

end ManuscriptAudit.KummerConstantCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerConstantCoefficients.constantToRoots_locallyInjective,
      ``ManuscriptAudit.KummerConstantCoefficients.constantToRoots_locallySurjective,
      ``ManuscriptAudit.KummerConstantCoefficients.constantRootSheafIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
