import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases

/-!
The \(Y\ne0\) coordinates of the plane cusp are \(X/Y=s\) and
\(Z/Y=s^3\). This file constructs the corresponding closed immersion
into the native affine chart of the projective plane. Its preimage
of \(Z\ne0\) is the connected nonempty basic open \(D(s)\).
-/

namespace ManuscriptAudit.CuspYChartAlgebra

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K]

abbrev PlaneRing := MvPolynomial (Fin 3) K
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 3) K
abbrev plane := Proj (grading K)

abbrev y : PlaneRing K := MvPolynomial.X (1 : Fin 3)
abbrev z : PlaneRing K := MvPolynomial.X (2 : Fin 3)

theorem X_mem_one (i : Fin 3) : (MvPolynomial.X i : PlaneRing K) ∈ grading K 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X K i)

private theorem C_mem_zero (c : K) : (MvPolynomial.C c : PlaneRing K) ∈ grading K 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C (Fin 3) c)

/-- Restrict the ordinary localization evaluation to fractions of degree zero. -/
def fractionEvaluation {B : Type*} [CommRing B] (eval : PlaneRing K →+* B)
    (f : PlaneRing K) (b : B) (hb : eval f * b = 1) :
    Away (grading K) f →+* B :=
  (Localization.awayLift eval f (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)).comp
    (algebraMap (Away (grading K) f) (Localization.Away f))

theorem fractionEvaluation_mk {B : Type*} [CommRing B] (eval : PlaneRing K →+* B)
    {f : PlaneRing K} {d : ℕ} (hf : f ∈ grading K d)
    (b : B) (hb : eval f * b = 1) (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • d)) :
    fractionEvaluation K eval f b hb (Away.mk (grading K) hf n p hp) = eval p * b ^ n := by
  change (Localization.awayLift eval f (isUnit_iff_exists_inv.mpr ⟨b, hb⟩))
    (Away.mk (grading K) hf n p hp).val = _
  rw [Away.val_mk]
  exact Localization.awayLift_mk eval f p b hb n

def yValues (i : Fin 3) : Polynomial K :=
  if i = 0 then Polynomial.X else if i = 1 then 1 else Polynomial.X ^ 3

def evalYPolynomial : PlaneRing K →ₐ[K] Polynomial K := MvPolynomial.aeval (yValues K)

private theorem evalY_y_mul_one : evalYPolynomial K (y K) * 1 = 1 := by
  simp [evalYPolynomial, yValues, y]

abbrev YChartRing := Away (grading K) (y K)

def evalYChart : YChartRing K →+* Polynomial K :=
  fractionEvaluation K (evalYPolynomial K).toRingHom (y K) 1 (evalY_y_mul_one K)

theorem evalYChart_mk (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • 1)) :
    evalYChart K (Away.mk (grading K) (X_mem_one K 1) n p hp) = evalYPolynomial K p := by
  unfold evalYChart
  rw [fractionEvaluation_mk, one_pow, mul_one]
  rfl

private def chartX : YChartRing K :=
  Away.mk (grading K) (X_mem_one K 1) 1 (MvPolynomial.X (0 : Fin 3))
    (by simpa only [one_nsmul] using X_mem_one K 0)

private def chartC (c : K) : YChartRing K :=
  Away.mk (grading K) (X_mem_one K 1) 0 (MvPolynomial.C c)
    (by simpa only [zero_nsmul] using C_mem_zero K c)

private theorem evalYChart_chartX : evalYChart K (chartX K) = Polynomial.X := by
  rw [chartX, evalYChart_mk]
  simp [evalYPolynomial, yValues]

private theorem evalYChart_chartC (c : K) : evalYChart K (chartC K c) = Polynomial.C c := by
  rw [chartC, evalYChart_mk]
  simp [evalYPolynomial, Polynomial.algebraMap_eq]

theorem evalYChart_surjective : Function.Surjective (evalYChart K) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | monomial n c =>
    refine ⟨chartC K c * chartX K ^ n, ?_⟩
    rw [map_mul, map_pow, evalYChart_chartC, evalYChart_chartX, Polynomial.C_mul_X_pow_eq_monomial]

abbrev yChartι : Spec (CommRingCat.of (YChartRing K)) ⟶ plane K :=
  Proj.awayι (grading K) (y K) (X_mem_one K 1) (by decide)

def lineInPlane : Spec (CommRingCat.of (Polynomial K)) ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (evalYChart K)) ≫ yChartι K

theorem lineInPlane_isImmersion : IsImmersion (lineInPlane K) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (evalYChart K))) :=
    IsClosedImmersion.spec_of_surjective _ (evalYChart_surjective K)
  unfold lineInPlane
  infer_instance

theorem lineInPlane_preimage_z :
    (lineInPlane K) ⁻¹ᵁ Proj.basicOpen (grading K) (z K) =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) := by
  unfold lineInPlane
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := grading K) (X_mem_one K 1) (by decide)
      (X_mem_one K 2) (by decide), SpecMap_preimage_basicOpen]
  have he :
      evalYChart K (Away.isLocalizationElem (X_mem_one K 1) (X_mem_one K 2)) =
        (Polynomial.X : Polynomial K) ^ 3 := by
    unfold Away.isLocalizationElem
    rw [evalYChart_mk, pow_one]
    simp [evalYPolynomial, yValues]
  change PrimeSpectrum.basicOpen
      (evalYChart K (Away.isLocalizationElem (X_mem_one K 1) (X_mem_one K 2))) = _
  rw [he, PrimeSpectrum.basicOpen_pow _ _ (by decide)]

theorem punctured_line_irreducible :
    IsIrreducible (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) :
      Set (PrimeSpectrum (Polynomial K))) := by
  let U := PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K)
  have h : (U : Set (PrimeSpectrum (Polynomial K))).Nonempty := by
    refine ⟨(⊥ : PrimeSpectrum (Polynomial K)), ?_⟩
    change (Polynomial.X : Polynomial K) ∉ (⊥ : Ideal (Polynomial K))
    exact fun hz => Polynomial.X_ne_zero (Ideal.mem_bot.mp hz)
  exact ⟨h, PreirreducibleSpace.isPreirreducible_univ.open_subset U.isOpen (Set.subset_univ _)⟩

/-- A homogeneous polynomial scales by the corresponding power of the common factor. -/
theorem aeval_scale {B : Type*} [CommRing B] [Algebra K B] (v : Fin 3 → B) (c : B)
    {n : ℕ} {p : PlaneRing K} (hp : p ∈ grading K n) :
    MvPolynomial.aeval (fun i => c * v i) p =
      c ^ n * MvPolynomial.aeval v p := by
  change p.IsWeightedHomogeneous (1 : Fin 3 → ℕ) n at hp
  refine MvPolynomial.IsWeightedHomogeneous.induction_on
    (motive := fun (q : PlaneRing K) _ =>
      MvPolynomial.aeval (fun i => c * v i) q = c ^ n * MvPolynomial.aeval v q)
    ?_ ?_ ?_ hp
  · simp only [map_zero, mul_zero]
  · intro f g _ _ hf hg
    simp only [map_add, hf, hg, mul_add]
  · intro d r hd
    simp only [MvPolynomial.aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    have hd' : (∑ i ∈ d.support, d i) = n := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using hd
    rw [hd']
    ac_rfl

end

end ManuscriptAudit.CuspYChartAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspYChartAlgebra.fractionEvaluation_mk,
      ``ManuscriptAudit.CuspYChartAlgebra.evalYChart_surjective,
      ``ManuscriptAudit.CuspYChartAlgebra.lineInPlane_isImmersion,
      ``ManuscriptAudit.CuspYChartAlgebra.lineInPlane_preimage_z,
      ``ManuscriptAudit.CuspYChartAlgebra.punctured_line_irreducible,
      ``ManuscriptAudit.CuspYChartAlgebra.aeval_scale] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
