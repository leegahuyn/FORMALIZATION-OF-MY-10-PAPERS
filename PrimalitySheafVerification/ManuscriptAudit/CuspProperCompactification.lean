import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured

/-!
# A proper compactification of the affine cusp

Embed the actual affine cusp with coordinate algebra \(K[t^2,t^3]\)
in the standard chart \(Z\ne0\) of the projective plane via
\(X/Z\mapsto t^2\), \(Y/Z\mapsto t^3\).
The schematic image of this quasi-compact immersion is proper over
\(K\), and the original affine cusp is a dense open subscheme.
-/

namespace ManuscriptAudit.CuspProperCompactification

open AlgebraicGeometry CategoryTheory HomogeneousLocalization CuspPunctured

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

private abbrev PlaneRing := MvPolynomial (Fin 3) K
private abbrev grading : ℕ → Submodule K (PlaneRing K) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) K

private abbrev z : PlaneRing K := MvPolynomial.X (2 : Fin 3)

private lemma X_mem_one (i : Fin 3) : (MvPolynomial.X i : PlaneRing K) ∈ grading K 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X K i)

private lemma C_mem_zero (a : K) : (MvPolynomial.C a : PlaneRing K) ∈ grading K 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C (Fin 3) a)

private abbrev ChartRing := Away (grading K) (z K)
private abbrev CuspRing := CuspSubalgebra K

private def cuspCube : CuspRing K :=
  ⟨(Polynomial.X : Polynomial K) ^ 3, Algebra.subset_adjoin (by simp)⟩

private def chartValues (i : Fin 3) : CuspRing K :=
  if i = 0 then cuspSquare K else if i = 1 then cuspCube K else 1

private def evalPolynomial : PlaneRing K →ₐ[K] CuspRing K :=
  MvPolynomial.aeval (chartValues K)

private lemma eval_z_mul_one : evalPolynomial K (z K) * 1 = 1 := by
  simp [evalPolynomial, chartValues, z]

/-- Evaluate a homogeneous degree-zero fraction at the affine cusp. -/
private def chartEvaluation : ChartRing K →+* CuspRing K :=
  (Localization.awayLift (evalPolynomial K).toRingHom (z K)
    (isUnit_iff_exists_inv.mpr ⟨1, eval_z_mul_one K⟩)).comp
      (algebraMap (ChartRing K) (Localization.Away (z K)))

private lemma chartEvaluation_mk (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • 1)) :
    chartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp) =
      evalPolynomial K p := by
  change (Localization.awayLift (evalPolynomial K).toRingHom (z K)
    (isUnit_iff_exists_inv.mpr ⟨1, eval_z_mul_one K⟩))
    (Away.mk (grading K) (X_mem_one K 2) n p hp).val = evalPolynomial K p
  rw [Away.val_mk]
  change (Localization.awayLift (evalPolynomial K).toRingHom (z K)
    (isUnit_iff_exists_inv.mpr ⟨1, eval_z_mul_one K⟩))
    (Localization.mk p ⟨(z K) ^ n, ⟨n, rfl⟩⟩) = (evalPolynomial K).toRingHom p
  simpa only [one_pow, mul_one] using
    Localization.awayLift_mk (evalPolynomial K).toRingHom (z K) p 1
      (eval_z_mul_one K) n

private lemma chartEvaluation_X (i : Fin 3) :
    chartEvaluation K (Away.mk (grading K) (X_mem_one K 2) 1 (MvPolynomial.X i)
      (by simpa only [one_nsmul] using X_mem_one K i)) = chartValues K i :=
  (chartEvaluation_mk K _ _ _).trans (MvPolynomial.aeval_X (chartValues K) i)

private lemma chartEvaluation_C (a : K) :
    chartEvaluation K (Away.mk (grading K) (X_mem_one K 2) 0 (MvPolynomial.C a)
      (by simpa only [zero_nsmul] using C_mem_zero K a)) = algebraMap K (CuspRing K) a :=
  (chartEvaluation_mk K _ _ _).trans (MvPolynomial.aeval_C (chartValues K) a)

private theorem chartEvaluation_surjective : Function.Surjective (chartEvaluation K) := by
  rintro ⟨p, hp⟩
  refine Algebra.adjoin_induction
    (p := fun a ha => ∃ q : ChartRing K, chartEvaluation K q = ⟨a, ha⟩)
    ?_ ?_ ?_ ?_ hp
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨_, by simpa [chartValues, cuspSquare] using chartEvaluation_X K 0⟩
    · exact ⟨_, by simpa [chartValues, cuspCube] using chartEvaluation_X K 1⟩
  · intro a
    exact ⟨_, chartEvaluation_C K a⟩
  · rintro a b _ _ ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨p + q, (map_add (chartEvaluation K) p q).trans (congrArg₂ (· + ·) hp hq)⟩
  · rintro a b _ _ ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨p * q, (map_mul (chartEvaluation K) p q).trans (congrArg₂ (· * ·) hp hq)⟩

private def constants : K →+* grading K 0 where
  toFun a := ⟨MvPolynomial.C a, C_mem_zero K a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)

private theorem constants_bijective : Function.Bijective (constants K) := by
  constructor
  · intro a b h
    exact MvPolynomial.C_injective (Fin 3) K (congrArg Subtype.val h)
  · intro p
    have hp : (p : PlaneRing K) ∈ (1 : Submodule K (PlaneRing K)) := by
      simpa only [grading, MvPolynomial.homogeneousSubmodule_zero] using p.property
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hp
    refine ⟨a, Subtype.ext ?_⟩
    change (MvPolynomial.C a : PlaneRing K) = (p : PlaneRing K)
    simpa only [MvPolynomial.algebraMap_eq] using ha

private instance constants_isIso : IsIso (CommRingCat.ofHom (constants K)) :=
  (RingEquiv.ofBijective (constants K) (constants_bijective K)).toCommRingCatIso.isIso_hom

private theorem variables_adjoin_eq_top :
    Algebra.adjoin (grading K 0) (Set.range (MvPolynomial.X : Fin 3 → PlaneRing K)) = ⊤ := by
  apply top_unique
  intro p hpTop
  clear hpTop
  induction p using MvPolynomial.induction_on with
  | C a =>
      change algebraMap (grading K 0) (PlaneRing K) (constants K a) ∈ _
      exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self i))

private instance planeRing_finiteType : Algebra.FiniteType (grading K 0) (PlaneRing K) := by
  classical
  constructor
  refine ⟨Finset.univ.image (MvPolynomial.X : Fin 3 → PlaneRing K), ?_⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using variables_adjoin_eq_top K

private abbrev plane := Proj (grading K)

private def planeToBase : plane K ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (grading K) ≫ Spec.map (CommRingCat.ofHom (constants K))

private instance planeToBase_isProper : IsProper (planeToBase K) := by
  unfold planeToBase
  infer_instance

private lemma chartEvaluation_constants (a : K) :
    chartEvaluation K (fromZeroRingHom (grading K) _ (constants K a)) =
      algebraMap K (CuspRing K) a := by
  change chartEvaluation K (Away.mk (grading K) (X_mem_one K 2) 0 (MvPolynomial.C a)
    (by simpa only [zero_nsmul] using C_mem_zero K a)) = _
  exact chartEvaluation_C K a

/-- The original affine cusp \(\operatorname{Spec} K[t^2,t^3]\). -/
abbrev affineCusp : Scheme.{u} := Spec (CommRingCat.of (CuspRing K))

/-- The standard immersion given by affine coordinates \(t^2,t^3\). -/
def cuspInPlane : affineCusp K ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (chartEvaluation K)) ≫
    Proj.awayι (grading K) (z K) (X_mem_one K 2) (by decide)

private instance cuspInPlane_isImmersion : IsImmersion (cuspInPlane K) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (chartEvaluation K))) :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective K)
  unfold cuspInPlane
  infer_instance

private instance cuspInPlane_quasiCompact : QuasiCompact (cuspInPlane K) :=
  quasiCompact_of_compactSpace _

/-- The schematic closure in the projective plane of the actual affine cusp.
This construction uses the embedding \(t\mapsto[t^2:t^3:1]\). -/
abbrev projectiveCusp : Scheme.{u} := (cuspInPlane K).image

def affineOpen : affineCusp K ⟶ projectiveCusp K := (cuspInPlane K).toImage

def projectiveCuspToBase : projectiveCusp K ⟶ Spec (CommRingCat.of K) :=
  (cuspInPlane K).imageι ≫ planeToBase K

theorem projectiveCusp_isProper : IsProper (projectiveCuspToBase K) := by
  unfold projectiveCuspToBase
  infer_instance

instance affineOpen_isOpenImmersion : IsOpenImmersion (affineOpen K) := by
  unfold affineOpen
  infer_instance

theorem affineOpen_isDominant : IsDominant (affineOpen K) := by
  unfold affineOpen
  infer_instance

theorem affineOpen_toBase :
    affineOpen K ≫ projectiveCuspToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (CuspRing K))) := by
  unfold affineOpen projectiveCuspToBase
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  unfold cuspInPlane planeToBase
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact chartEvaluation_constants K

/-- The homogeneous cubic \(Y^2Z-X^3\) vanishing on the projective cusp. -/
def planeCubic : PlaneRing K :=
  MvPolynomial.X (1 : Fin 3) ^ 2 * z K - MvPolynomial.X (0 : Fin 3) ^ 3

private theorem planeCubic_mem : planeCubic K ∈ grading K 3 := by
  change MvPolynomial.IsHomogeneous (planeCubic K) 3
  exact (((MvPolynomial.isHomogeneous_X K (1 : Fin 3)).pow 2).mul
    (MvPolynomial.isHomogeneous_X K (2 : Fin 3))).sub
      ((MvPolynomial.isHomogeneous_X K (0 : Fin 3)).pow 3)

private theorem evalPlaneCubic_zero : evalPolynomial K (planeCubic K) = 0 := by
  simp only [planeCubic, evalPolynomial, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, z]
  change cuspCube K ^ 2 * (1 : CuspRing K) - cuspSquare K ^ 3 = 0
  apply Subtype.ext
  change (((Polynomial.X : Polynomial K) ^ 3) ^ 2 * 1 - (Polynomial.X ^ 2) ^ 3) = 0
  ring

private abbrev zChartι : Spec (CommRingCat.of (ChartRing K)) ⟶ plane K :=
  Proj.awayι (grading K) (z K) (X_mem_one K 2) (by decide)

private abbrev cuspToZChart : affineCusp K ⟶ Spec (CommRingCat.of (ChartRing K)) :=
  Spec.map (CommRingCat.ofHom (chartEvaluation K))

private theorem cuspInPlane_avoids_cubic_open (x : affineCusp K) :
    cuspInPlane K x ∉ Proj.basicOpen (grading K) (planeCubic K) := by
  intro h
  change cuspToZChart K x ∈ (zChartι K) ⁻¹ᵁ Proj.basicOpen (grading K) (planeCubic K) at h
  rw [Proj.awayι_preimage_basicOpen (𝒜 := grading K) (X_mem_one K 2) (by decide)
    (planeCubic_mem K) (by decide)] at h
  have hn := (PrimeSpectrum.mem_basicOpen _ _).mp h
  apply hn
  change chartEvaluation K (Away.isLocalizationElem (X_mem_one K 2) (planeCubic_mem K)) ∈
    (x : PrimeSpectrum (CuspRing K)).asIdeal
  have hZero :
      chartEvaluation K (Away.isLocalizationElem (X_mem_one K 2) (planeCubic_mem K)) = 0 := by
    unfold Away.isLocalizationElem
    rw [chartEvaluation_mk, pow_one, evalPlaneCubic_zero]
  rw [hZero]
  exact (x : PrimeSpectrum (CuspRing K)).asIdeal.zero_mem

private theorem image_range_eq_closure :
    Set.range (cuspInPlane K).imageι = closure (Set.range (cuspInPlane K)) := by
  change Set.range (cuspInPlane K).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

/-- Every point of the proper closure lies on the homogeneous cubic. -/
theorem cubic_mem_projectiveCusp (x : projectiveCusp K) :
    planeCubic K ∈ ((cuspInPlane K).imageι x).asHomogeneousIdeal := by
  classical
  have hSubset : closure (Set.range (cuspInPlane K)) ⊆
      ((Proj.basicOpen (grading K) (planeCubic K) : Set (plane K)))ᶜ :=
    closure_minimal (by rintro _ ⟨p, rfl⟩; exact cuspInPlane_avoids_cubic_open K p)
      (Proj.basicOpen (grading K) (planeCubic K)).isOpen.isClosed_compl
  have hx : (cuspInPlane K).imageι x ∈ Set.range (cuspInPlane K).imageι := ⟨x, rfl⟩
  rw [image_range_eq_closure] at hx
  by_contra hn
  exact (hSubset hx) ((Proj.mem_basicOpen _ _ _).mpr hn)

private theorem mem_affine_image_of_z_open (x : projectiveCusp K)
    (hx : (cuspInPlane K).imageι x ∈ Proj.basicOpen (grading K) (z K)) :
    x ∈ Set.range (affineOpen K) := by
  have hi : (cuspInPlane K).imageι x ∈ Set.range (zChartι K) := by
    change (cuspInPlane K).imageι x ∈ (zChartι K).opensRange
    rw [Proj.opensRange_awayι]
    exact hx
  obtain ⟨q, hq⟩ := hi
  have hqClosure : zChartι K q ∈ closure (Set.range (cuspInPlane K)) := by
    rw [hq, ← image_range_eq_closure]
    exact ⟨x, rfl⟩
  haveI : IsClosedImmersion (cuspToZChart K) :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective K)
  have hClosed := (cuspToZChart K).isClosedEmbedding.isClosed_range
  have hRange : Set.range (cuspInPlane K) = (zChartι K) '' Set.range (cuspToZChart K) := by
    change Set.range ((zChartι K) ∘ (cuspToZChart K)) = _
    exact Set.range_comp _ _
  have he := (zChartι K).isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
    (Set.range (cuspToZChart K))
  rw [hClosed.closure_eq, ← hRange] at he
  have hqImage : q ∈ Set.range (cuspToZChart K) := by
    rw [he]
    exact hqClosure
  obtain ⟨t, ht⟩ := hqImage
  refine ⟨t, (cuspInPlane K).imageι.isClosedEmbedding.injective ?_⟩
  calc
    _ = cuspInPlane K t := by
      change ((affineOpen K) ≫ (cuspInPlane K).imageι) t = _
      rw [affineOpen, Scheme.Hom.toImage_imageι]
    _ = zChartι K q := by
      change zChartι K (cuspToZChart K t) = _
      rw [ht]
    _ = _ := hq

/-- Outside the affine chart the image in the projective plane is supported
where \(X\) and \(Z\) vanish and \(Y\) does not vanish. -/
theorem boundary_plane_coordinates (x : projectiveCusp K)
    (hx : x ∉ Set.range (affineOpen K)) :
    (MvPolynomial.X (0 : Fin 3) : PlaneRing K) ∈ ((cuspInPlane K).imageι x).asHomogeneousIdeal ∧
      (MvPolynomial.X (2 : Fin 3) : PlaneRing K) ∈ ((cuspInPlane K).imageι x).asHomogeneousIdeal ∧
      (MvPolynomial.X (1 : Fin 3) : PlaneRing K) ∉ ((cuspInPlane K).imageι x).asHomogeneousIdeal := by
  classical
  let p := (cuspInPlane K).imageι x
  have hz : z K ∈ p.asHomogeneousIdeal := by
    by_contra hn
    exact hx (mem_affine_image_of_z_open K x ((Proj.mem_basicOpen _ _ _).mpr hn))
  have hc : (MvPolynomial.X (1 : Fin 3)) ^ 2 * z K -
      (MvPolynomial.X (0 : Fin 3)) ^ 3 ∈ p.asHomogeneousIdeal.toIdeal :=
    cubic_mem_projectiveCusp K x
  have hMul := p.asHomogeneousIdeal.toIdeal.mul_mem_left ((MvPolynomial.X (1 : Fin 3)) ^ 2)
    (show z K ∈ p.asHomogeneousIdeal.toIdeal from hz)
  have hCube : (MvPolynomial.X (0 : Fin 3) : PlaneRing K) ^ 3 ∈ p.asHomogeneousIdeal.toIdeal := by
    simpa only [sub_sub_cancel] using p.asHomogeneousIdeal.toIdeal.sub_mem hMul hc
  have ha : (MvPolynomial.X (0 : Fin 3) : PlaneRing K) ∈ p.asHomogeneousIdeal :=
    p.isPrime.mem_of_pow_mem 3 hCube
  have hCover := Proj.iSup_basicOpen_eq_top' (grading K)
    (MvPolynomial.X : Fin 3 → PlaneRing K) (fun i => ⟨1, X_mem_one K i⟩)
    (variables_adjoin_eq_top K)
  have hTop : p ∈ (⊤ : (plane K).Opens) := trivial
  rw [← hCover] at hTop
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hTop
  have hni := (Proj.mem_basicOpen _ _ _).mp hi
  refine ⟨ha, hz, ?_⟩
  fin_cases i
  · exact (hni ha).elim
  · exact hni
  · exact (hni hz).elim

/-- Restriction of functions on the \(Z\ne0\) plane chart to the affine cusp. -/
abbrev affineChartEvaluation := chartEvaluation K

theorem affineChartEvaluation_mk_coe (n : ℕ) (p : PlaneRing K)
    (hp : p ∈ grading K (n • 1)) :
    ((affineChartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp)) : Polynomial K) =
      MvPolynomial.aeval (fun i : Fin 3 =>
        if i = 0 then (Polynomial.X : Polynomial K) ^ 2
        else if i = 1 then Polynomial.X ^ 3 else 1) p := by
  unfold affineChartEvaluation
  rw [chartEvaluation_mk]
  change ((CuspSubalgebra K).val.comp (evalPolynomial K)) p = _
  unfold evalPolynomial
  rw [MvPolynomial.comp_aeval]
  apply congrArg (fun coords : Fin 3 → Polynomial K => MvPolynomial.aeval coords p)
  funext i
  fin_cases i <;> rfl

abbrev affineZChartι := zChartι K

theorem cuspInPlane_as_Z_chart :
    cuspInPlane K = Spec.map (CommRingCat.ofHom (affineChartEvaluation K)) ≫ affineZChartι K :=
  rfl

theorem affineOpen_opensRange_eq :
    (affineOpen K).opensRange =
      (cuspInPlane K).imageι ⁻¹ᵁ Proj.basicOpen (grading K) (z K) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change ((affineOpen K) ≫ (cuspInPlane K).imageι) t ∈ Proj.basicOpen (grading K) (z K)
    rw [affineOpen, Scheme.Hom.toImage_imageι, ← Proj.opensRange_awayι (grading K) (z K)
      (X_mem_one K 2) (by decide)]
    exact ⟨cuspToZChart K t, rfl⟩
  · intro h
    exact mem_affine_image_of_z_open K x h

end

end ManuscriptAudit.CuspProperCompactification

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspProperCompactification.projectiveCusp_isProper,
      ``ManuscriptAudit.CuspProperCompactification.affineOpen_isOpenImmersion,
      ``ManuscriptAudit.CuspProperCompactification.affineOpen_isDominant,
      ``ManuscriptAudit.CuspProperCompactification.affineOpen_toBase,
      ``ManuscriptAudit.CuspProperCompactification.cubic_mem_projectiveCusp,
      ``ManuscriptAudit.CuspProperCompactification.boundary_plane_coordinates,
      ``ManuscriptAudit.CuspProperCompactification.affineChartEvaluation_mk_coe,
      ``ManuscriptAudit.CuspProperCompactification.cuspInPlane_as_Z_chart,
      ``ManuscriptAudit.CuspProperCompactification.affineOpen_opensRange_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
