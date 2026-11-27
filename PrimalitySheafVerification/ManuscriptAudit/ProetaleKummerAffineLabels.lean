import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerCoefficientMap

/-! A root section on an affine pro-étale chart is locally a unique
constant coefficient root, using the actual idempotent localizations. -/

namespace ManuscriptAudit.ProetaleKummerAffineLabels

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleKummerRoots ProetaleKummerPower ProetaleKummerCoefficientMap
open KummerRootLabels

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))
  {R : CommRingCat.{0}} (g : Spec R ⟶ X) [WeaklyEtale g] (d : ℕ)

/-- An equal pair of coefficient sections is locally equal on an actual
affine chart, also on the empty spectrum. -/
theorem equalizer_mem (x y : coefficientGroup K d)
    (h : (constantToRoots k d).app (op (Scheme.ProEt.mk g)) x =
        (constantToRoots k d).app (op (Scheme.ProEt.mk g)) y) :
    Presheaf.equalizerSieve (F := (Functor.const X.ProEtᵒᵖ).obj (coefficientGroup K d)) x y ∈
      J X (Scheme.ProEt.mk g) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    letI : IsEmpty (Scheme.ProEt.mk g).left := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    exact (J X).superset_covering bot_le (Scheme.ProEt.bot_mem_topology (Scheme.ProEt.mk g))
  · letI := hR
    have h' := congrArg (specRoots d g) h
    rw [specRoots_coefficient, specRoots_coefficient] at h'
    have hxy : x = y := by
      apply ULift.ext
      apply Additive.ext
      apply rootsOfUnity.coe_injective
      apply (affineCoefficients k g).hom.injective
      exact congrArg (fun a : Additive (rootsOfUnity d R) ↦ ((a.toMul : Rˣ) : R)) h'
    rw [hxy, Presheaf.equalizerSieve_self_eq_top]
    exact (J X).top_mem _

private theorem affineCoefficients_comp {T : CommRingCat.{0}} (r : R ⟶ T)
    [WeaklyEtale (Spec.map r ≫ g)] :
    affineCoefficients k g ≫ r = affineCoefficients k (Spec.map r ≫ g) := by
  apply Spec.map_injective
  change Spec.map (Spec.preimage (g ≫ k) ≫ r) =
    Spec.map (Spec.preimage ((Spec.map r ≫ g) ≫ k))
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc]

variable [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

/-- The actual image sieve of the constant-root map covers any displayed
affine chart where the degree is invertible. -/
theorem image_mem (s : (roots X d).obj (op (Scheme.ProEt.mk g))) :
    Presheaf.imageSieve (constantToRoots k d) s ∈ J X (Scheme.ProEt.mk g) := by
  let U := Scheme.ProEt.mk g
  let a : rootsOfUnity d R := (specRoots d g s).toMul
  letI : Algebra K R := (affineCoefficients k g).hom.toAlgebra
  choose e _he hFiber using fun ζ : rootsOfUnity d K ↦ locallyConstantRootTag_idempotent a ζ
  let B (ζ : rootsOfUnity d K) := Localization.Away (e ζ)
  let r (ζ : rootsOfUnity d K) : R ⟶ CommRingCat.of (B ζ) :=
    CommRingCat.ofHom (algebraMap R (B ζ))
  let em (ζ : rootsOfUnity d K) := Spec.map (r ζ)
  letI hOpen (ζ : rootsOfUnity d K) : IsOpenImmersion (em ζ) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := R) (e ζ)
  let V (ζ : rootsOfUnity d K) : X.ProEt := Scheme.ProEt.mk (em ζ ≫ g)
  let f (ζ : rootsOfUnity d K) : V ζ ⟶ U := MorphismProperty.Over.homMk (em ζ) rfl
  have hRange (ζ : rootsOfUnity d K) :
      Set.range (PrimeSpectrum.comap (r ζ).hom) = PrimeSpectrum.basicOpen (e ζ) :=
    PrimeSpectrum.localization_away_comap_range (B ζ) (e ζ)
  have hc : Sieve.ofArrows V f ∈ J X U := by
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.ofArrows V f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage (Spec R)
    rw [Presieve.map_ofArrows]
    apply Scheme.etalePrecoverage_le_proetalePrecoverage _
    change Presieve.ofArrows (fun ζ ↦ Spec (CommRingCat.of (B ζ))) em ∈
      Scheme.precoverage @Etale (Spec R)
    apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
    refine ⟨fun P ↦ ?_, fun ζ ↦ inferInstanceAs (Etale (em ζ))⟩
    let ζ := locallyConstantRootTag (K := K) a P
    have hP : P ∈ (PrimeSpectrum.basicOpen (e ζ) : Set (PrimeSpectrum R)) := by
      rw [← hFiber ζ]
      rfl
    rw [← hRange ζ] at hP
    exact ⟨ζ, hP⟩
  apply (J X).superset_covering _ hc
  change Sieve.generate (Presieve.ofArrows V f) ≤ _
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro ζ
  rw [Presheaf.imageSieve_apply]
  refine ⟨⟨Additive.ofMul ζ⟩, (specRoots d (em ζ ≫ g)).injective ?_⟩
  rw [specRoots_coefficient, specRoots_natural d g (r ζ)]
  apply Additive.ext
  letI : Algebra K (B ζ) := (affineCoefficients k (em ζ ≫ g)).hom.toAlgebra
  let alg : R →ₐ[K] B ζ :=
    { toRingHom := (r ζ).hom
      commutes' x := congrArg (fun a : CommRingCat.of K ⟶ CommRingCat.of (B ζ) ↦ a.hom x)
        (affineCoefficients_comp k g (r ζ)) }
  change mapRoots d (algebraMap K (B ζ)) ζ = mapRoots d alg.toRingHom a
  apply locallyConstantRootTag_injective (K := K)
  apply LocallyConstant.ext
  intro Q
  rw [locallyConstantRootTag_coeff, locallyConstantRootTag_natural]
  have hQ : PrimeSpectrum.comap (r ζ).hom Q ∈
      (PrimeSpectrum.basicOpen (e ζ) : Set (PrimeSpectrum R)) := by
    rw [← hRange ζ]
    exact ⟨Q, rfl⟩
  rw [← hFiber ζ] at hQ
  change locallyConstantRootTag (K := K) a (PrimeSpectrum.comap (r ζ).hom Q) = ζ at hQ
  exact hQ.symm

end
end ManuscriptAudit.ProetaleKummerAffineLabels

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerAffineLabels.equalizer_mem,
      ``ManuscriptAudit.ProetaleKummerAffineLabels.image_mem] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
