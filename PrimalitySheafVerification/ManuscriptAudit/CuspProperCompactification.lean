import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Homogeneous
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

private instance planeRing_finiteType : Algebra.FiniteType (grading K 0) (PlaneRing K) := by
  classical
  constructor
  refine ⟨Finset.univ.image (MvPolynomial.X : Fin 3 → PlaneRing K), ?_⟩
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
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

theorem affineOpen_isOpenImmersion : IsOpenImmersion (affineOpen K) := by
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

end

end ManuscriptAudit.CuspProperCompactification

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspProperCompactification.projectiveCusp_isProper,
      ``ManuscriptAudit.CuspProperCompactification.affineOpen_isOpenImmersion,
      ``ManuscriptAudit.CuspProperCompactification.affineOpen_isDominant,
      ``ManuscriptAudit.CuspProperCompactification.affineOpen_toBase] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
