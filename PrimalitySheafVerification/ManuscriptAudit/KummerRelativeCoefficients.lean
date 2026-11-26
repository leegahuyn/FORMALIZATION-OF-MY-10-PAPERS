import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerConstantCoefficients

/-! Relative coefficient roots for the affine étale basis of an
arbitrary scheme over an algebraically closed field. -/

namespace ManuscriptAudit.KummerRelativeCoefficients

open AlgebraicGeometry CategoryTheory Opposite
open KummerRootLabels KummerUnitsPresheaf
open KummerConstantCoefficients (roots coefficientGroup)

universe u

noncomputable section

variable {K : Type u} [Field K] {X : Scheme.{u}} (k : X ⟶ Spec (CommRingCat.of K))

def coefficientMap (U : X.AffineEtale) : K →+* coordinateRing U :=
  (Scheme.Spec.preimage (U.hom ≫ k) : U.left ⟶ op (CommRingCat.of K)).unop.hom

theorem coefficientMap_natural {U V : X.AffineEtale} (f : U ⟶ V) :
    f.left.unop.hom.comp (coefficientMap k V) = coefficientMap k U := by
  let cU : U.left ⟶ op (CommRingCat.of K) := Scheme.Spec.preimage (U.hom ≫ k)
  let cV : V.left ⟶ op (CommRingCat.of K) := Scheme.Spec.preimage (V.hom ≫ k)
  have h : f.left ≫ cV = cU := by
    apply Scheme.Spec.map_injective
    have hf : Scheme.Spec.map f.left ≫ V.hom = U.hom := by
      have hh := f.w
      change Scheme.Spec.map f.left ≫ V.hom = U.hom ≫ 𝟙 X at hh
      exact hh.trans (Category.comp_id _)
    rw [Scheme.Spec.map_comp]
    change Scheme.Spec.map f.left ≫ Scheme.Spec.map (Scheme.Spec.preimage (V.hom ≫ k)) =
      Scheme.Spec.map (Scheme.Spec.preimage (U.hom ≫ k))
    rw [Scheme.Spec.map_preimage, Scheme.Spec.map_preimage]
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ k) hf)
  have hp := congrArg (fun a : U.left ⟶ op (CommRingCat.of K) => a.unop.hom) h
  rw [unop_comp, CommRingCat.hom_comp] at hp
  exact hp

/-- The canonical map from the constant coefficient roots. -/
def constantToRoots (d : ℕ) :
    (Functor.const (X.AffineEtaleᵒᵖ)).obj (coefficientGroup K d) ⟶ roots X d where
  app U := AddCommGrpCat.ofHom (mapRoots d (coefficientMap k U.unop)).toAdditive
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro a
    apply Additive.ext
    apply Subtype.ext
    apply Units.ext
    let a₀ : rootsOfUnity d K := (show Additive (rootsOfUnity d K) from a).toMul
    change coefficientMap k V.unop ((a₀ : Kˣ) : K) =
      f.unop.left.unop.hom (coefficientMap k U.unop ((a₀ : Kˣ) : K))
    exact (DFunLike.congr_fun (coefficientMap_natural k f.unop) ((a₀ : Kˣ) : K)).symm

private theorem affine_family_cover_iff {X : Scheme.{u}} {U : X.AffineEtale}
    {ι : Type*} {V : ι → X.AffineEtale} (f : ∀ i, V i ⟶ U) :
    Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology X U ↔
      ⋃ i, Set.range (Scheme.Spec.map (f i).left) = Set.univ := by
  rw [Scheme.AffineEtale.topology, Functor.mem_inducedTopology_iff_of_isCoverDense,
    Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff] <;> rfl

/-- The constant-root map is locally injective, including at the empty affine
scheme, where the empty family covers. -/
theorem constantToRoots_locallyInjective (d : ℕ) :
    Presheaf.IsLocallyInjective (Scheme.AffineEtale.topology X)
      (constantToRoots (K := K) k d) where
  equalizerSieve_mem {U} x y h := by
    let A := coordinateRing U.unop
    rcases subsingleton_or_nontrivial A with hA | hA
    · letI : Subsingleton A := hA
      let f : ∀ _ : Empty, U.unop ⟶ U.unop := fun _ => 𝟙 U.unop
      have hc : Sieve.ofArrows (fun _ : Empty => U.unop) f ∈
          Scheme.AffineEtale.topology X U.unop := by
        rw [affine_family_cover_iff]
        apply Set.eq_univ_of_forall
        intro P
        change PrimeSpectrum A at P
        exact isEmptyElim P
      apply (Scheme.AffineEtale.topology X).superset_covering _ hc
      change Sieve.generate (Presieve.ofArrows (fun _ : Empty => U.unop) f) ≤ _
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro i
      exact isEmptyElim i
    · letI : Nontrivial A := hA
      have hxy : x = y := by
        apply Additive.ext
        apply rootsOfUnity.coe_injective
        apply (coefficientMap (K := K) k U.unop).injective
        exact congrArg (fun a : Additive (rootsOfUnity d A) => ((a.toMul : Aˣ) : A)) h
      rw [hxy, Presheaf.equalizerSieve_self_eq_top]
      exact (Scheme.AffineEtale.topology X).top_mem _

variable {d : ℕ} [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

/-- Each root section is the image of a constant coefficient root locally.
The actual covers are the affine opens cut out by the fiber idempotents. -/
theorem constantToRoots_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.AffineEtale.topology X)
      (constantToRoots (K := K) k d) where
  imageSieve_mem {U} s := by
    let A := coordinateRing U
    letI : Algebra K A := (coefficientMap (K := K) k U).toAlgebra
    let a : rootsOfUnity d A := (show Additive (rootsOfUnity d A) from s).toMul
    choose e _he hFiber using fun ζ : rootsOfUnity d K =>
      locallyConstantRootTag_idempotent a ζ
    let B := fun ζ => Localization.Away (e ζ)
    let r : ∀ ζ, A →+* B ζ := fun ζ => algebraMap A (B ζ)
    let eMap : ∀ ζ, Spec (CommRingCat.of (B ζ)) ⟶ Spec A :=
      fun ζ => AlgebraicGeometry.Spec.map (CommRingCat.ofHom (r ζ))
    let g : Spec A ⟶ X := U.hom
    letI : Etale g := U.prop
    let V : rootsOfUnity d K → X.AffineEtale := fun ζ => by
      letI : IsOpenImmersion (eMap ζ) :=
        Scheme.isOpenImmersion_SpecMap_localizationAway (R := A) (e ζ)
      exact Scheme.AffineEtale.mk (eMap ζ ≫ g)
    let f : ∀ ζ, V ζ ⟶ U := fun ζ =>
      MorphismProperty.CostructuredArrow.homMk (CommRingCat.ofHom (r ζ)).op trivial rfl
    have hRange (ζ : rootsOfUnity d K) :
        Set.range (PrimeSpectrum.comap (r ζ)) = PrimeSpectrum.basicOpen (e ζ) :=
      PrimeSpectrum.localization_away_comap_range (B ζ) (e ζ)
    have hc : Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology X U := by
      apply (affine_family_cover_iff f).mpr
      change ⋃ ζ, Set.range (PrimeSpectrum.comap (r ζ)) = Set.univ
      apply Set.eq_univ_of_forall
      intro P
      let ζ := locallyConstantRootTag (K := K) a P
      have hP : P ∈ (PrimeSpectrum.basicOpen (e ζ) : Set (PrimeSpectrum A)) := by
        rw [← hFiber ζ] <;> rfl
      rw [← hRange ζ] at hP
      exact Set.mem_iUnion.mpr ⟨ζ, hP⟩
    apply (Scheme.AffineEtale.topology X).superset_covering _ hc
    change Sieve.generate (Presieve.ofArrows V f) ≤ _
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro ζ
    rw [Presheaf.imageSieve_apply]
    refine ⟨Additive.ofMul ζ, ?_⟩
    apply Additive.ext
    change mapRoots d (coefficientMap k (V ζ)) ζ = mapRoots d (r ζ) a
    letI : Algebra K (B ζ) := (coefficientMap (K := K) k (V ζ)).toAlgebra
    let alg : A →ₐ[K] B ζ :=
      { toRingHom := r ζ
        commutes' x := DFunLike.congr_fun (coefficientMap_natural (K := K) k (f ζ)) x }
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
    (constantSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}).obj
        (coefficientGroup K d) ≅
      (presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}).obj
        (roots X d) := by
  let J := Scheme.AffineEtale.topology X
  let η := constantToRoots (K := K) k d
  have hW : J.W η := (J.W_iff_isLocallyBijective η).mpr
    ⟨constantToRoots_locallyInjective (K := K) k d,
      constantToRoots_locallySurjective (K := K) (d := d) k⟩
  let f : (constantSheaf J AddCommGrpCat.{u}).obj (coefficientGroup K d) ⟶
      (presheafToSheaf J AddCommGrpCat.{u}).obj (roots X d) :=
    (presheafToSheaf J AddCommGrpCat.{u}).map η
  have hf : IsIso f := (J.W_iff η).mp hW
  exact @asIso (Sheaf J AddCommGrpCat.{u}) _ _ _ f hf

end
end ManuscriptAudit.KummerRelativeCoefficients

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.KummerRelativeCoefficients.constantRootSheafIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
