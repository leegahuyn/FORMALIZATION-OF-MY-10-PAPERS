import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineIdealDegree

/-! Degree on actual geometric affine fractional ideals, with explicit
denominator-independence. -/

namespace ManuscriptAudit.WeierstrassFractionalIdealDegree

open FractionalIdeal WeierstrassCurve.Affine WeierstrassAffineIdealDegree
open scoped nonZeroDivisors

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev F := W.FunctionField
private abbrev Fractional := FractionalIdeal (A W)⁰ (F W)

local instance : IsDedekindDomain (A W) :=
  WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W

private abbrev p (a : A W) : Ideal (A W) := Ideal.span {a}
private abbrev s (a : A W) : Fractional W := spanSingleton (A W)⁰ (algebraMap (A W) (F W) a)

private theorem span_ne_zero {a : A W} (ha : a ≠ 0) : p W a ≠ 0 := by
  rwa [p, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]

private theorem integral_representation (I : Fractional W) :
    ∃ a : A W, ∃ J : Ideal (A W), a ≠ 0 ∧ (J : Fractional W) = s W a * I := by
  obtain ⟨a, J, ha, h⟩ := exists_eq_spanSingleton_mul I
  refine ⟨a, J, ha, ?_⟩
  have hmap : algebraMap (A W) (F W) a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  rw [h, ← mul_assoc, spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hmap,
    spanSingleton_one, one_mul]

private theorem num_ne_zero {I : Fractional W} (hI : I ≠ 0)
    {a : A W} (ha : a ≠ 0) {J : Ideal (A W)}
    (hJ : (J : Fractional W) = s W a * I) : J ≠ 0 := by
  intro hz
  have hs : s W a ≠ 0 := spanSingleton_ne_zero_iff.mpr
    (IsFractionRing.to_map_eq_zero_iff.not.mpr ha)
  apply mul_ne_zero hs hI
  rw [← hJ, hz, Ideal.zero_eq_bot, coeIdeal_bot]

/-- The signed quotient degree is independent of the clearing denominator. -/
theorem signed_degree_eq {I : Fractional W} (hI : I ≠ 0)
    {a b : A W} (ha : a ≠ 0) (hb : b ≠ 0) {J L : Ideal (A W)}
    (hJ : (J : Fractional W) = s W a * I)
    (hL : (L : Fractional W) = s W b * I) :
    (degree W J : ℤ) - degree W (p W a) =
      (degree W L : ℤ) - degree W (p W b) := by
  have hc : p W b * J = p W a * L := by
    apply coeIdeal_injective (K := F W)
    change ((p W b * J : Ideal (A W)) : Fractional W) =
      ((p W a * L : Ideal (A W)) : Fractional W)
    rw [coeIdeal_mul, coeIdeal_mul, coeIdeal_span_singleton, coeIdeal_span_singleton, hJ, hL]
    change s W b * (s W a * I) = s W a * (s W b * I)
    ac_rfl
  have hd := congrArg (degree W) hc
  rw [degree_mul W (span_ne_zero W hb) (num_ne_zero W hI ha hJ),
    degree_mul W (span_ne_zero W ha) (num_ne_zero W hI hb hL)] at hd
  omega

private def denominator (I : Fractional W) : A W :=
  (integral_representation W I).choose

private def numerator (I : Fractional W) : Ideal (A W) :=
  (integral_representation W I).choose_spec.choose

private theorem representation (I : Fractional W) :
    denominator W I ≠ 0 ∧ (numerator W I : Fractional W) = s W (denominator W I) * I :=
  (integral_representation W I).choose_spec.choose_spec

/-- Actual degree of a fractional ideal given by integral degrees of a
cleared numerator and its principal denominator. -/
def fractionalDegree (I : Fractional W) : ℤ :=
  (degree W (numerator W I) : ℤ) - degree W (p W (denominator W I))

theorem fractionalDegree_eq {I : Fractional W} (hI : I ≠ 0)
    {a : A W} (ha : a ≠ 0) {J : Ideal (A W)} (hJ : (J : Fractional W) = s W a * I) :
    fractionalDegree W I = (degree W J : ℤ) - degree W (p W a) :=
  signed_degree_eq W hI (representation W I).1 ha (representation W I).2 hJ

/-- Degree is a sum under multiplication of nonzero fractional ideals. -/
theorem fractionalDegree_mul (I J : Fractional W) (hI : I ≠ 0) (hJ : J ≠ 0) :
    fractionalDegree W (I * J) = fractionalDegree W I + fractionalDegree W J := by
  let a := denominator W I
  let b := denominator W J
  let M := numerator W I
  let N := numerator W J
  have ha : a ≠ 0 := (representation W I).1
  have hb : b ≠ 0 := (representation W J).1
  have hM : (M : Fractional W) = s W a * I := (representation W I).2
  have hN : (N : Fractional W) = s W b * J := (representation W J).2
  have hMN : ((M * N : Ideal (A W)) : Fractional W) = s W (a * b) * (I * J) := by
    rw [coeIdeal_mul, hM, hN]
    change (s W a * I) * (s W b * J) =
      spanSingleton (A W)⁰ (algebraMap (A W) (F W) (a * b)) * (I * J)
    rw [map_mul, ← spanSingleton_mul_spanSingleton]
    ac_rfl
  rw [fractionalDegree_eq W (mul_ne_zero hI hJ) (mul_ne_zero ha hb) hMN,
    fractionalDegree_eq W hI ha hM, fractionalDegree_eq W hJ hb hN,
    degree_mul W (num_ne_zero W hI ha hM) (num_ne_zero W hJ hb hN)]
  have hp : p W (a * b) = p W a * p W b := (Ideal.span_singleton_mul_span_singleton a b).symm
  rw [hp, degree_mul W (span_ne_zero W ha) (span_ne_zero W hb)]
  omega

end

end ManuscriptAudit.WeierstrassFractionalIdealDegree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassFractionalIdealDegree.signed_degree_eq,
      ``ManuscriptAudit.WeierstrassFractionalIdealDegree.fractionalDegree_eq,
      ``ManuscriptAudit.WeierstrassFractionalIdealDegree.fractionalDegree_mul] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
