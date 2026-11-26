import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.EllipticFiniteDescent
import PrimalitySheafVerification.ManuscriptAudit.Paper5FixedGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.Paper5FixedPositiveTraceZero

/-!
# Geometric p-torsion of the fixed positive-parameter Paper 5 model

The finite-field quadratic-partner count is valid over every finite
extension of a good residue field. It transfers the point count modulo
the residue characteristic from the fixed `j = 1728` example to the
fixed printed-family model `y² = x³ - 11x + 14`.
-/

namespace ManuscriptAudit.Paper5FixedPositiveGeometricTorsion

open FiniteFieldPointCount (shortCubic)

noncomputable section

private theorem partner_comparison {F : Type*} [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (hchar : ringChar F ≠ 2) :
    (∑ x : F, quadraticChar F (x ^ 3 - x)) =
      ∑ x : F, quadraticChar F (x ^ 3 - 11 * x + 14) := by
  have h := Paper5FixedPositiveTraceZero.quadratic_partner_character_sum h2 hchar (-3) 2 h2
  change (∑ x : F, quadraticChar F (x ^ 3 + (-3 : F) * x ^ 2 + 2 * x)) =
    (∑ x : F, quadraticChar F (x ^ 3 - 2 * (-3 : F) * x ^ 2 +
      ((-3 : F) ^ 2 - 4 * 2) * x)) at h
  have hs (x : F) : x ^ 3 + (-3 : F) * x ^ 2 + 2 * x = (x + (-1)) ^ 3 - (x + (-1)) := by
    ring
  have ht (x : F) : x ^ 3 - 2 * (-3 : F) * x ^ 2 + ((-3 : F) ^ 2 - 4 * 2) * x =
      (x + 2) ^ 3 - 11 * (x + 2) + 14 := by
    ring
  simp_rw [hs, ht] at h
  exact (Equiv.sum_comp (Equiv.addRight (-1 : F)) (fun x : F => quadraticChar F (x ^ 3 - x))).symm.trans
    (h.trans (Equiv.sum_comp (Equiv.addRight (2 : F))
      (fun x : F => quadraticChar F (x ^ 3 - 11 * x + 14))))

theorem projective_count_cast_eq_one {F : Type*} [Field F] [Fintype F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp5 : 5 ≤ p) (hp4 : p % 4 = 3) :
    (Nat.card (shortCubic (11 : F) 14).toProjective.Point : F) = 1 := by
  classical
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; omega
  have h2 : (2 : F) ≠ 0 := by
    have hn : ¬ p ∣ (2 : ℕ) := by
      intro h
      have hh := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) h
      omega
    simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero_iff F p 2).not.mpr hn
  have hDelta : (shortCubic (11 : F) 14).Δ = (shortCubic (2 : F) 0).Δ := by
    simp [shortCubic, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;> ring
  have hGood : (shortCubic (11 : F) 14).Δ ≠ 0 := by
    rw [hDelta]
    exact Paper5FixedGeometricTorsion.shortCubic_linear_discriminant_ne_zero hp5 h2
  have hGood' := Paper5FixedGeometricTorsion.shortCubic_linear_discriminant_ne_zero hp5
    (one_ne_zero : (1 : F) ≠ 0)
  have hOne := Paper5FixedGeometricTorsion.projective_count_cast_eq_one hp5 hp4
    (one_ne_zero : (1 : F) ≠ 0)
  have hOdd := FiniteField.odd_card_of_char_ne_two hchar
  have hExp : (Fintype.card F - 1) / 2 = Fintype.card F / 2 := by omega
  have hCast (g : F → F) :
      ((∑ x : F, quadraticChar F (g x) : ℤ) : F) =
        ∑ x : F, g x ^ ((Fintype.card F - 1) / 2) := by
    rw [Int.cast_sum, hExp]
    simp_rw [quadraticChar_eq_pow_of_char_ne_two' hchar]
  have hSum := partner_comparison h2 hchar
  rw [FiniteFieldPointCount.shortCubic_projective_count_cast hchar hGood'] at hOne
  simp only [one_mul, add_zero] at hOne
  rw [FiniteFieldPointCount.shortCubic_projective_count_cast hchar hGood,
    ← hCast (fun x : F => x ^ 3 - 11 * x + 14), ← hSum,
    hCast (fun x : F => x ^ 3 - x)]
  exact hOne

private theorem reduction_baseChange_eq_short {p : ℕ} [Fact p.Prime] {L : Type*}
    [Field L] [Algebra (ZMod p) L] :
    (Paper5FixedPositiveTraceZero.reduction p).baseChange L = shortCubic (11 : L) 14 := by
  simp [Paper5FixedPositiveTraceZero.reduction, Paper5FixedPositiveTraceZero.fixedCurve, shortCubic,
    WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]

private theorem finite_affine_no_p_torsion {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Fintype L] [DecidableEq L] [Algebra (ZMod p) L] (hp5 : 5 ≤ p) (hp4 : p % 4 = 3) :
    ∀ Q : ((Paper5FixedPositiveTraceZero.reduction p).baseChange L).toAffine.Point,
      p • Q = 0 → Q = 0 := by
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  rw [reduction_baseChange_eq_short]
  intro Q hQ
  let e := (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := (shortCubic (11 : L) 14).toProjective)).symm
  have hT : p • e Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  have hz := Paper5FixedGeometricTorsion.torsion_eq_zero_of_card_cast_one
    (projective_count_cast_eq_one (F := L) hp5 hp4) (e Q) hT
  apply e.injective
  simpa only [map_zero] using hz

theorem fixed_curve_no_geometric_p_torsion {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]
    (hp5 : 5 ≤ p) (hp4 : p % 4 = 3)
    (P : ((Paper5FixedPositiveTraceZero.reduction p).baseChange L).toProjective.Point)
    (hP : p • P = 0) : P = 0 := by
  classical
  let e := WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := ((Paper5FixedPositiveTraceZero.reduction p).baseChange L).toProjective)
  apply e.injective
  rw [map_zero]
  refine EllipticFiniteDescent.torsion_eq_zero_of_finite_fields
    (Paper5FixedPositiveTraceZero.reduction p).toAffine p ?_ (e P) ?_
  · intro E hE
    letI : Finite E := hE
    letI := Fintype.ofFinite E
    letI : DecidableEq E := inferInstanceAs (DecidableEq {x : L // x ∈ E})
    exact finite_affine_no_p_torsion (L := E) hp5 hp4
  · rw [← map_nsmul, hP, map_zero]

def geometricTorsionTrivial (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ P : ((Paper5FixedPositiveTraceZero.reduction p).baseChange
      (AlgebraicClosure (ZMod p))).toProjective.Point, p • P = 0 → P = 0

theorem arbitrarily_large_good_geometric_torsion_trivial (N : ℕ) :
    ∃ (p : ℕ) (hp : p.Prime), N < p ∧ 14 < p ∧ p % 4 = 3 ∧
      (Paper5FixedPositiveTraceZero.reduction p).Δ ≠ 0 ∧ geometricTorsionTrivial p hp := by
  obtain ⟨p, hN, hp, hp14, hp4, hDelta, _⟩ :=
    Paper5FixedPositiveTraceZero.arbitrarily_large_good_trace_zero_primes N
  have hp5 : 5 ≤ p := by omega
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, hN, hp14, hp4, hDelta, fun P hP => fixed_curve_no_geometric_p_torsion hp5 hp4 P hP⟩

end

end ManuscriptAudit.Paper5FixedPositiveGeometricTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5FixedPositiveGeometricTorsion.projective_count_cast_eq_one,
      ``ManuscriptAudit.Paper5FixedPositiveGeometricTorsion.fixed_curve_no_geometric_p_torsion,
      ``ManuscriptAudit.Paper5FixedPositiveGeometricTorsion.arbitrarily_large_good_geometric_torsion_trivial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
