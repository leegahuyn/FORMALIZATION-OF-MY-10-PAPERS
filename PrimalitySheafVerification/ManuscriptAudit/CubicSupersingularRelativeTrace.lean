import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCenteredFrobeniusPowers
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularTatePointCount

/-! Signed projective counts over all relative extensions of an even-degree base. -/

namespace ManuscriptAudit.CubicSupersingularRelativeTrace

open Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicNonsplitFrobeniusTrace PowerTateModule
open CubicCenteredFrobeniusPowers CubicSupersingularTatePointCount

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [Algebra E L]
variable (D : Type*) [Field D] [Fintype D] [DecidableEq D] [Algebra (ZMod p) D]
variable [Algebra E D] [IsScalarTower (ZMod p) E D] [Algebra D L] [IsScalarTower E D L]

/-- Native Frobenius powers recover the signed point count over any actual finite extension. -/
theorem trace_pow_eq_point_count (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    {m : ℕ} (hm : finrank (ZMod p) E = 2 * m) (hm₀ : 0 < m)
    {A : E} (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A))
      ((endMap l (arithmeticPointFrobenius E L A)) ^ finrank E D) =
      (Int.cast ((Fintype.card D : ℤ) + 1 -
        (Nat.card (shortCubic (0 : D) (algebraMap E D A)).toProjective.Point : ℤ)) : ℤ_[l]) := by
  let n := finrank E D
  have hPos : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    have hc : Fintype.card D = Fintype.card E ^ n := Module.card_eq_pow_finrank (K := E) (V := D)
    rw [hn, pow_zero] at hc
    exact (ne_of_gt (Fintype.one_lt_card : 1 < Fintype.card D)) hc
  have hmD : finrank (ZMod p) D = 2 * (m * n) := by
    rw [← Module.finrank_mul_finrank (ZMod p) E D, hm, mul_assoc]
  let a := algebraMap E D A
  have ha : a ≠ 0 := (map_ne_zero (algebraMap E D)).mpr hA
  let W := Curve a
  let V := Curve (algebraMap E L A)
  let hW : W.baseChange L = V :=
    (centered_baseChange D L a).trans (congrArg Curve (IsScalarTower.algebraMap_apply E D L A).symm)
  let g := FiniteField.frobeniusAlgHom D L
  have aux {V' : Affine L} (he : Curve (algebraMap D L a) = V') :
      LinearMap.trace ℤ_[l] (Tate l V'.Point)
        (endMap l (pointMapAt D L W V' ((centered_baseChange D L a).trans he) g)) =
        (Int.cast ((Fintype.card D : ℤ) + 1 -
          (Nat.card (shortCubic (0 : D) a).toProjective.Point : ℤ)) : ℤ_[l]) := by
    subst V'
    exact (trace_det_eq_point_count p L l D hp hp₃ hlp hmD (Nat.mul_pos hm₀ hPos) ha).1
  have hF : arithmeticPointFrobenius E L A ^ n = pointMapAt D L W V hW g :=
    arithmetic_power_eq E L D A
  rw [← map_pow, hF]
  exact aux (congrArg Curve (IsScalarTower.algebraMap_apply E D L A).symm)

end
end ManuscriptAudit.CubicSupersingularRelativeTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularRelativeTrace.trace_pow_eq_point_count
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
