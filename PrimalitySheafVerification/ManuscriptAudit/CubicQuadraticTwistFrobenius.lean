import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSexticTwists

/-! The native Frobenius of the quadratic twist is the negative conjugate. -/

namespace ManuscriptAudit.CubicQuadraticTwistFrobenius

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicPointScaling CubicFrobeniusSexticTwists

noncomputable section

variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

theorem quadratic_twist_parameter {A d : E} (hA : A ≠ 0) (hd : ¬ IsSquare d)
    (hchar : ringChar E ≠ 2) {k : ℕ} (hq : Fintype.card E = 6 * k + 1) :
    parameter A (d ^ 3 * A) k = -1 := by
  have hdiv : (d ^ 3 * A) / A = d ^ 3 := ((eq_div_iff hA).mpr rfl).symm
  have hk : 3 * k = Fintype.card E / 2 := by omega
  rw [parameter, hdiv, ← pow_mul, hk]
  have hχ : quadraticChar E d = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hd
  simpa only [hχ, Int.cast_neg, Int.cast_one] using
    (quadraticChar_eq_pow_of_char_ne_two' hchar d).symm

private theorem scale_eq_neg {L : Type*} [Field L] [DecidableEq L] {B v : L}
    (hv : v ≠ 0) (hV : v ^ 6 * B = B) (hΔ : (shortCubic (0 : L) B).Δ ≠ 0)
    (hvneg : v = -1) (P : (Curve B).Point) :
    scale hv hV hΔ P = -P := by
  subst v
  cases P with
  | zero =>
    change scale hv hV hΔ (0 : (Curve B).Point) = -0
    simp only [map_zero, neg_zero]
  | some x y h =>
    rw [scale_some, Affine.Point.neg_some, Affine.Point.some.injEq]
    constructor
    · norm_num
    · simp [Curve, CubicAffine, shortCubic, Affine.negY, pow_succ]

variable (E) (L : Type*) [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

/-- The actual finite-field Frobenius on the twist is conjugate to negation composed with
the actual Frobenius of the original centered cubic. -/
theorem exists_neg_conjugacy {A d : E} (hA : A ≠ 0) (hd : ¬ IsSquare d)
    (hchar : ringChar E ≠ 2) {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L (d ^ 3 * A))).Δ ≠ 0) :
    ∃ e : Geometric E L A ≃+ Geometric E L (d ^ 3 * A), ∀ P,
      arithmeticFrobenius E L (d ^ 3 * A) (e P) = e (-arithmeticFrobenius E L A P) := by
  have hd₀ : d ≠ 0 := fun h => hd (h.symm ▸ IsSquare.zero)
  have hB : d ^ 3 * A ≠ 0 := mul_ne_zero (pow_ne_zero _ hd₀) hA
  obtain ⟨hv, hV, e, he⟩ := exists_conjugacy E L hA hB hq hΔA hΔB
  have hneg : algebraMap E L (parameter A (d ^ 3 * A) k) = -1 := by
    rw [quadratic_twist_parameter hA hd hchar hq, map_neg, map_one]
  exact ⟨e, fun P => (he P).trans (congrArg e
    (scale_eq_neg hv hV hΔA hneg (arithmeticFrobenius E L A P)))⟩

end
end ManuscriptAudit.CubicQuadraticTwistFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicQuadraticTwistFrobenius.quadratic_twist_parameter,
      ``ManuscriptAudit.CubicQuadraticTwistFrobenius.exists_neg_conjugacy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
