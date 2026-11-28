import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartAlgebra
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveBoundary
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveInfinityExists

/-! The actual proper closure adds exactly one geometric point. -/

namespace ManuscriptAudit.WeierstrassProjectiveInfinity

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification WeierstrassProjectiveClosure

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

private abbrev P := MvPolynomial (Fin 3) K
private abbrev g := standardPlaneGrading K
private abbrev X : P K := MvPolynomial.X (0 : Fin 3)
private abbrev Y : P K := MvPolynomial.X (1 : Fin 3)
private abbrev Z : P K := MvPolynomial.X (2 : Fin 3)

private def values (i : Fin 3) : K := if i = 1 then 1 else 0
private def scalarValues (i : Fin 3) : P K := algebraMap K (P K) (values K i)

private abbrev substitute : P K →ₐ[K] P K :=
  MvPolynomial.aeval (fun i => Y K * scalarValues K i)

private theorem substitute_eval (p : P K) {n : ℕ} (hp : p ∈ g K n) :
    substitute K p = Y K ^ n * algebraMap K (P K) (MvPolynomial.aeval (values K) p) := by
  have ha : MvPolynomial.aeval (scalarValues K) =
      (Algebra.ofId K (P K)).comp (MvPolynomial.aeval (values K)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [scalarValues]
  rw [substitute, CuspYChartAlgebra.aeval_scale K _ _ hp, ha] <;> rfl

private theorem homogeneous_mem_iff (p : projectivePlane K)
    (hx : X K ∈ p.asHomogeneousIdeal) (hz : Z K ∈ p.asHomogeneousIdeal)
    (hy : Y K ∉ p.asHomogeneousIdeal) {n : ℕ} {f : P K} (hf : f ∈ g K n) :
    f ∈ p.asHomogeneousIdeal ↔ MvPolynomial.aeval (values K) f = 0 := by
  let I := p.asHomogeneousIdeal.toIdeal
  let q := Ideal.Quotient.mkₐ K I
  have hx0 : q (X K) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hz0 : q (Z K) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hq : q.comp (substitute K) = q := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply]
    change q (MvPolynomial.aeval (fun j => Y K * scalarValues K j) (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    fin_cases i
    · simpa [scalarValues, values] using hx0.symm
    · simp [scalarValues, values]
    · simpa [scalarValues, values] using hz0.symm
  have hqf : q (substitute K f) = q f := AlgHom.congr_fun hq f
  have hScale := substitute_eval K f hf
  constructor
  · intro h
    have hE : substitute K f ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hqf.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h))
    rw [hScale] at hE
    have hY : Y K ^ n ∉ I := fun h => hy (p.isPrime.mem_of_pow_mem n h)
    have hC : algebraMap K (P K) (MvPolynomial.aeval (values K) f) ∈ I :=
      (p.isPrime.mem_or_mem hE).resolve_left hY
    by_contra hn
    have hU := (isUnit_iff_ne_zero.mpr hn).map (algebraMap K (P K))
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem I hC hU)
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q f = 0
    exact hqf.symm.trans (by rw [hScale, h, map_zero, mul_zero, map_zero])

private theorem plane_at_infinity_eq (p q : projectivePlane K)
    (hp : X K ∈ p.asHomogeneousIdeal ∧ Z K ∈ p.asHomogeneousIdeal ∧ Y K ∉ p.asHomogeneousIdeal)
    (hq : X K ∈ q.asHomogeneousIdeal ∧ Z K ∈ q.asHomogeneousIdeal ∧ Y K ∉ q.asHomogeneousIdeal) :
    p = q := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n f hf
  exact (homogeneous_mem_iff K p hp.1 hp.2.1 hp.2.2 hf).trans
    (homogeneous_mem_iff K q hq.1 hq.2.1 hq.2.2 hf).symm

variable {K}

/-- The complement of the actual affine Weierstrass chart consists of one point. -/
theorem existsUnique_boundary (W : WeierstrassCurve.Affine K) :
    ∃! x : projectiveScheme W, x ∉ Set.range (WeierstrassProjectiveClosure.affineOpen W) := by
  obtain ⟨x, hx⟩ := WeierstrassProjectiveInfinityExists.exists_boundary W
  refine ⟨x, hx, fun y hy => (inPlane W).imageι.isClosedEmbedding.injective ?_⟩
  exact plane_at_infinity_eq K _ _
    (WeierstrassProjectiveBoundary.boundary_plane_coordinates W y hy)
    (WeierstrassProjectiveBoundary.boundary_plane_coordinates W x hx)

end

end ManuscriptAudit.WeierstrassProjectiveInfinity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveInfinity.existsUnique_boundary
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
