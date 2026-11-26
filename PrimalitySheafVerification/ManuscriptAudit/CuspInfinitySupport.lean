import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CuspRationalInfinity

/-!
The projective-plane point where \(X=Z=0\) and \(Y\ne0\) is unique.
For a homogeneous polynomial of degree \(d\), putting \(X=Z=0\)
leaves a scalar multiple of \(Y^d\). Its membership in a relevant
homogeneous prime with these coordinates is thus determined by that
scalar. Applied to the proper cusp, this identifies its entire
topological boundary with the rational infinity point.
-/

namespace ManuscriptAudit.CuspInfinitySupport

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification CuspRationalInfinity

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K]

private abbrev A := MvPolynomial (Fin 3) K
private abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 3) K
private abbrev planeY : A K := MvPolynomial.X (1 : Fin 3)

private def keepY : A K →ₐ[K] A K :=
  MvPolynomial.aeval fun i => if i = (1 : Fin 3) then planeY K else 0

private theorem keepY_X (i : Fin 3) :
    keepY K (MvPolynomial.X i) = if i = (1 : Fin 3) then planeY K else 0 :=
  MvPolynomial.aeval_X _ _

private theorem keepY_sub_mem (I : Ideal (A K))
    (hX : MvPolynomial.X (0 : Fin 3) ∈ I) (hZ : MvPolynomial.X (2 : Fin 3) ∈ I)
    (p : A K) : p - keepY K p ∈ I := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : keepY K (MvPolynomial.C a) = MvPolynomial.C a := by
      simp [keepY, MvPolynomial.algebraMap_eq]
    rw [hC, sub_self]
    exact I.zero_mem
  | add p q hp hq =>
    rw [map_add]
    have he : p + q - (keepY K p + keepY K q) =
        (p - keepY K p) + (q - keepY K q) := by ring
    rw [he]
    exact I.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, keepY_X]
    fin_cases i
    · rw [if_neg (by decide), mul_zero, sub_zero]
      exact I.mul_mem_left p hX
    · change (p * planeY K - keepY K p *
        (if (1 : Fin 3) = 1 then planeY K else 0)) ∈ I
      rw [if_pos rfl, ← sub_mul]
      exact I.mul_mem_right _ hp
    · rw [if_neg (by decide), mul_zero, sub_zero]
      exact I.mul_mem_left p hZ

private theorem mem_iff_keepY_mem (I : Ideal (A K))
    (hX : MvPolynomial.X (0 : Fin 3) ∈ I) (hZ : MvPolynomial.X (2 : Fin 3) ∈ I)
    (p : A K) : p ∈ I ↔ keepY K p ∈ I := by
  have hd := keepY_sub_mem K I hX hZ p
  constructor
  · intro hp
    have h := I.sub_mem hp hd
    rwa [sub_sub_cancel] at h
  · intro hp
    have h := I.add_mem hd hp
    rwa [sub_add_cancel] at h

private theorem keepY_map_one :
    (grading K 1).map (keepY K).toLinearMap = Submodule.span K ({planeY K} : Set (A K)) := by
  change (MvPolynomial.homogeneousSubmodule (Fin 3) K 1).map (keepY K).toLinearMap = _
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨i, rfl⟩
    change keepY K (MvPolynomial.X i) ∈ _
    rw [keepY_X]
    split
    · exact Submodule.subset_span (by simp)
    · exact Submodule.zero_mem _
  · rintro _ hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    apply Submodule.subset_span
    refine ⟨(1 : Fin 3), ?_⟩
    change keepY K (MvPolynomial.X (1 : Fin 3)) = planeY K
    rw [keepY_X, if_pos rfl]

private theorem keepY_homogeneous {n : ℕ} {p : A K} (hp : p ∈ grading K n) :
    ∃ c : K, c • (planeY K) ^ n = keepY K p := by
  have hm : (grading K n).map (keepY K).toLinearMap =
      Submodule.span K ({(planeY K) ^ n} : Set (A K)) := by
    have hGrade : (grading K 1) ^ n = grading K n :=
      MvPolynomial.homogeneousSubmodule_one_pow (σ := Fin 3) (R := K) n
    rw [← hGrade, Submodule.map_pow, keepY_map_one]
    exact (map_pow (Submodule.spanSingleton K) (planeY K) n).symm
  have hMem : keepY K p ∈ (grading K n).map (keepY K).toLinearMap :=
    Submodule.mem_map_of_mem hp
  rw [hm] at hMem
  exact Submodule.mem_span_singleton.mp hMem

private theorem scalar_mul_y_pow_mem_iff (p : ProjectiveSpectrum (grading K))
    (hy : planeY K ∉ p.asHomogeneousIdeal) (c : K) (n : ℕ) :
    c • (planeY K) ^ n ∈ p.asHomogeneousIdeal.toIdeal ↔ c = 0 := by
  constructor
  · intro h
    rw [Algebra.smul_def] at h
    rcases p.isPrime.mem_or_mem h with hC | hY
    · by_contra hn
      have hUnit : IsUnit (algebraMap K (A K) c) :=
        (isUnit_iff_ne_zero.mpr hn).map (algebraMap K (A K))
      exact p.isPrime.ne_top (p.asHomogeneousIdeal.toIdeal.eq_top_of_isUnit_mem hC hUnit)
    · exact (hy (p.isPrime.mem_of_pow_mem n hY)).elim
  · rintro rfl
    rw [zero_smul]
    exact p.asHomogeneousIdeal.toIdeal.zero_mem

/-- Uniqueness of the projective-plane point with coordinates \([0:1:0]\). -/
theorem projectivePlane_infinity_unique (p q : ProjectiveSpectrum (grading K))
    (hpX : MvPolynomial.X (0 : Fin 3) ∈ p.asHomogeneousIdeal)
    (hpZ : MvPolynomial.X (2 : Fin 3) ∈ p.asHomogeneousIdeal)
    (hpY : planeY K ∉ p.asHomogeneousIdeal)
    (hqX : MvPolynomial.X (0 : Fin 3) ∈ q.asHomogeneousIdeal)
    (hqZ : MvPolynomial.X (2 : Fin 3) ∈ q.asHomogeneousIdeal)
    (hqY : planeY K ∉ q.asHomogeneousIdeal) : p = q := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n f hf
  obtain ⟨c, hc⟩ := keepY_homogeneous K hf
  change f ∈ p.asHomogeneousIdeal.toIdeal ↔ f ∈ q.asHomogeneousIdeal.toIdeal
  rw [mem_iff_keepY_mem K p.asHomogeneousIdeal.toIdeal hpX hpZ,
    mem_iff_keepY_mem K q.asHomogeneousIdeal.toIdeal hqX hqZ,
    ← hc, scalar_mul_y_pow_mem_iff K p hpY, scalar_mul_y_pow_mem_iff K q hqY]

/-- Every point outside the affine cusp is the value of the rational infinity section. -/
theorem boundary_eq_infinityPoint (x : projectiveCusp K)
    (hx : x ∉ Set.range (affineOpen K)) :
    x = infinityPoint K (IsLocalRing.closedPoint K) := by
  obtain ⟨hX, hZ, hY⟩ := boundary_plane_coordinates K x hx
  obtain ⟨hiX, hiZ, hiY⟩ := boundary_plane_coordinates K _ (infinityPoint_outside K)
  apply (cuspInPlane K).imageι.isClosedEmbedding.injective
  exact projectivePlane_infinity_unique K _ _ hX hZ hY hiX hiZ hiY

/-- The reduced rational infinity point accounts for the whole boundary support. -/
theorem affine_complement_eq_infinity :
    (Set.range (affineOpen K))ᶜ = Set.range (infinityPoint K) := by
  ext x
  constructor
  · intro hx
    exact ⟨IsLocalRing.closedPoint K, (boundary_eq_infinityPoint K x hx).symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hy]
    exact infinityPoint_outside K

end

end ManuscriptAudit.CuspInfinitySupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspInfinitySupport.projectivePlane_infinity_unique,
      ``ManuscriptAudit.CuspInfinitySupport.boundary_eq_infinityPoint,
      ``ManuscriptAudit.CuspInfinitySupport.affine_complement_eq_infinity] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
