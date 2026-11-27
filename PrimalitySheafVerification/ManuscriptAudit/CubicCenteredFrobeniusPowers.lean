import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace

/-! Relative extension Frobenius on the actual centered curve is an iterate. -/

namespace ManuscriptAudit.CubicCenteredFrobeniusPowers

open Module WeierstrassCurve CubicThreeTorsionOrdinate
open CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace

noncomputable section

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [IsAlgClosed L]
variable [DecidableEq L]

theorem power_some (A : E) (n : ℕ) {x y : L}
    (h : (Curve (algebraMap E L A)).Nonsingular x y) :
    ∃ h', (arithmeticPointFrobenius E L A ^ n) (Affine.Point.some x y h) =
      Affine.Point.some (x ^ (Fintype.card E ^ n)) (y ^ (Fintype.card E ^ n)) h' := by
  let V := Curve (algebraMap E L A)
  let f := arithmeticPointFrobenius E L A
  let q := Fintype.card E
  induction n with
  | zero =>
    have h' : V.Nonsingular (x ^ (q ^ 0)) (y ^ (q ^ 0)) := by simpa only [pow_zero, pow_one] using h
    refine ⟨h', ?_⟩
    rw [pow_zero]
    change Affine.Point.some x y h = Affine.Point.some (x ^ (q ^ 0)) (y ^ (q ^ 0)) h'
    rw [Affine.Point.some.injEq]
    simp only [pow_zero, pow_one, and_self]
  | succ n ih =>
    obtain ⟨h₁, e₁⟩ := ih
    let g := FiniteField.frobeniusAlgHom E L
    obtain ⟨h₂, e₂⟩ := pointMapAt_some E L (Curve A) V (centered_baseChange E L A)
      g (x ^ (q ^ n)) (y ^ (q ^ n)) h₁
    have hm (z : L) : g (z ^ (q ^ n)) = z ^ (q ^ (n + 1)) := by
      change (z ^ (q ^ n)) ^ q = z ^ (q ^ (n + 1))
      rw [← pow_mul, pow_succ]
    have h' : V.Nonsingular (x ^ (q ^ (n + 1))) (y ^ (q ^ (n + 1))) := by
      simpa only [hm] using h₂
    refine ⟨h', ?_⟩
    rw [pow_succ']
    change f ((f ^ n) (Affine.Point.some x y h)) = _
    rw [e₁]
    change pointMapAt E L (Curve A) V (centered_baseChange E L A) g
      (Affine.Point.some (x ^ (q ^ n)) (y ^ (q ^ n)) h₁) = _
    rw [e₂, Affine.Point.some.injEq]
    exact ⟨hm x, hm y⟩

variable (D : Type*) [Field D] [Fintype D] [Algebra E D] [Algebra D L] [IsScalarTower E D L]

/-- Keep the geometric curve fixed while enlarging the finite arithmetic base. -/
theorem arithmetic_power_eq (A : E) :
    let W := Curve (algebraMap E D A)
    let V := Curve (algebraMap E L A)
    let hW : W.baseChange L = V :=
      (centered_baseChange D L (algebraMap E D A)).trans
        (congrArg Curve (IsScalarTower.algebraMap_apply E D L A).symm)
    arithmeticPointFrobenius E L A ^ finrank E D =
      pointMapAt D L W V hW (FiniteField.frobeniusAlgHom D L) := by
  let W := Curve (algebraMap E D A)
  let V := Curve (algebraMap E L A)
  let hW : W.baseChange L = V :=
    (centered_baseChange D L (algebraMap E D A)).trans
      (congrArg Curve (IsScalarTower.algebraMap_apply E D L A).symm)
  let g := FiniteField.frobeniusAlgHom D L
  let n := finrank E D
  change arithmeticPointFrobenius E L A ^ n = pointMapAt D L W V hW g
  have hCard : Fintype.card D = Fintype.card E ^ n := Module.card_eq_pow_finrank (K := E) (V := D)
  apply AddMonoidHom.ext
  intro P
  cases P with
  | zero =>
    change (arithmeticPointFrobenius E L A ^ n) (0 : V.Point) = pointMapAt D L W V hW g 0
    simp only [map_zero]
  | some x y h =>
    obtain ⟨h₁, he₁⟩ := power_some E L A n h
    obtain ⟨h₂, he₂⟩ := pointMapAt_some D L W V hW g x y h
    refine he₁.trans (Eq.trans ?_ he₂.symm)
    rw [Affine.Point.some.injEq]
    change x ^ (Fintype.card E ^ n) = x ^ Fintype.card D ∧
      y ^ (Fintype.card E ^ n) = y ^ Fintype.card D
    simp only [hCard, and_self]

end
end ManuscriptAudit.CubicCenteredFrobeniusPowers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCenteredFrobeniusPowers.power_some,
      ``ManuscriptAudit.CubicCenteredFrobeniusPowers.arithmetic_power_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
