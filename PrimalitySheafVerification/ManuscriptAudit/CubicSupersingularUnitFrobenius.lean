import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusExtensionFixed

/-! Even-degree Frobenius on the unit centered twist is a scalar on geometric points. -/

namespace ManuscriptAudit.CubicSupersingularUnitFrobenius

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicHermitianFrobeniusSquare WeierstrassFrobeniusExtensionFixed
open scoped Classical

noncomputable section

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [DecidableEq L]

abbrev UnitPoints := (Curve (1 : L)).Point

theorem unit_baseChange : (Curve (1 : E)).baseChange L = Curve (1 : L) :=
  (centered_baseChange E L 1).trans (congrArg Curve (map_one (algebraMap E L)))

def unitMap (g : L →ₐ[E] L) : AddMonoid.End (UnitPoints L) :=
  pointMapAt E L (Curve (1 : E)) (Curve (1 : L)) (unit_baseChange E L) g

theorem unitMap_some (g : L →ₐ[E] L) {x y : L} (h : (Curve (1 : L)).Nonsingular x y) :
    ∃ h', unitMap E L g (Affine.Point.some x y h) = Affine.Point.some (g x) (g y) h' :=
  pointMapAt_some E L (Curve (1 : E)) (Curve (1 : L)) (unit_baseChange E L) g x y h

theorem unitMap_pow (g : L →ₐ[E] L) (n : ℕ) :
    unitMap E L (g ^ n) = unitMap E L g ^ n := by
  have hOne : unitMap E L (1 : L →ₐ[E] L) = 1 := by
    apply AddMonoidHom.ext
    intro P
    cases P with
    | zero => exact map_zero _
    | some x y h =>
      change unitMap E L (1 : L →ₐ[E] L) (.some x y h) = .some x y h
      obtain ⟨h', e⟩ := unitMap_some E L (1 : L →ₐ[E] L) h
      exact e
  have hMul (f g : L →ₐ[E] L) :
      unitMap E L (f * g) = unitMap E L f * unitMap E L g := by
    apply AddMonoidHom.ext
    intro P
    change unitMap E L (f * g) P = unitMap E L f (unitMap E L g P)
    cases P with
    | zero =>
      change unitMap E L (f * g) (0 : UnitPoints L) = unitMap E L f (unitMap E L g 0)
      simp only [map_zero]
    | some x y h =>
      obtain ⟨h₁, e₁⟩ := unitMap_some E L (f * g) h
      obtain ⟨h₂, e₂⟩ := unitMap_some E L g h
      obtain ⟨h₃, e₃⟩ := unitMap_some E L f h₂
      rw [e₁, e₂, e₃] <;> rfl
  induction n with
  | zero => simpa only [pow_zero] using hOne
  | succ n ih => rw [pow_succ, pow_succ, hMul, ih]

abbrev arithmeticUnit : AddMonoid.End (UnitPoints L) :=
  unitMap E L (FiniteField.frobeniusAlgHom E L)

variable (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] [Algebra (ZMod p) E]

/-- The arithmetic unit twists over the two bases act by the same coordinate powers. -/
theorem arithmeticUnit_eq_prime_pow :
    arithmeticUnit E L = arithmeticUnit (ZMod p) L ^ Module.finrank (ZMod p) E := by
  let g := FiniteField.frobeniusAlgHom (ZMod p) L
  let d := Module.finrank (ZMod p) E
  calc
    arithmeticUnit E L = unitMap (ZMod p) L (g ^ d) := by
      apply AddMonoidHom.ext
      intro P
      have hCard : Fintype.card E = p ^ d := by
        rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card]
      cases P with
      | zero =>
        change unitMap E L (FiniteField.frobeniusAlgHom E L) (0 : UnitPoints L) =
          unitMap (ZMod p) L (g ^ d) 0
        simp only [map_zero]
      | some x y h =>
        change unitMap E L (FiniteField.frobeniusAlgHom E L) (.some x y h) =
          unitMap (ZMod p) L (g ^ d) (.some x y h)
        obtain ⟨h₁, e₁⟩ := unitMap_some E L (FiniteField.frobeniusAlgHom E L) h
        obtain ⟨h₂, e₂⟩ := unitMap_some (ZMod p) L (g ^ d) h
        refine e₁.trans (Eq.trans ?_ e₂.symm)
        rw [Affine.Point.some.injEq]
        constructor
        · exact (congrArg (fun n : ℕ => x ^ n) hCard).trans
            (pow_frobenius_apply p L d x).symm
        · exact (congrArg (fun n : ℕ => y ^ n) hCard).trans
            (pow_frobenius_apply p L d y).symm
    _ = _ := unitMap_pow (ZMod p) L g d

variable [IsAlgClosed L]

theorem prime_square (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (P : UnitPoints L) :
    arithmeticUnit (ZMod p) L (arithmeticUnit (ZMod p) L P) = -(p • P) := by
  obtain ⟨h₂, h₃⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have hp₂ : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with h | h
    · omega
    · omega
  have hCard : Fintype.card (ZMod p) = p := ZMod.card p
  have aux {V : Affine L} (hV : (Curve (1 : ZMod p)).baseChange L = V) (P : V.Point) :
      let F := pointMapAt (ZMod p) L (Curve (1 : ZMod p)) V hV
        (FiniteField.frobeniusAlgHom (ZMod p) L)
      F (F P) = -(p • P) := by
    subst V
    simpa only [hCard] using frobenius_sq_eq_neg_card (ZMod p) L h₂ h₃ one_ne_zero
      (by simpa only [hCard] using hp₃) (by simpa only [hCard] using hp₂) P
  exact aux (unit_baseChange (ZMod p) L) P

/-- At degree 2m the genuine q-Frobenius on the reference curve is multiplication by (-p)^m. -/
theorem arithmeticUnit_eq_scalar (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    {m : ℕ} (hDegree : Module.finrank (ZMod p) E = 2 * m) :
    arithmeticUnit E L = Int.cast ((-(p : ℤ)) ^ m) := by
  let f := arithmeticUnit (ZMod p) L
  have hs : f ^ 2 = Int.cast (-(p : ℤ)) := by
    apply AddMonoidHom.ext
    intro P
    rw [pow_two, Int.cast_neg, Int.cast_natCast]
    change f (f P) = -(p • P)
    exact prime_square L p hp hp₃ P
  rw [arithmeticUnit_eq_prime_pow E L p, hDegree, pow_mul, hs, Int.cast_pow]

end
end ManuscriptAudit.CubicSupersingularUnitFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSupersingularUnitFrobenius.unitMap_pow,
      ``ManuscriptAudit.CubicSupersingularUnitFrobenius.arithmeticUnit_eq_prime_pow,
      ``ManuscriptAudit.CubicSupersingularUnitFrobenius.prime_square,
      ``ManuscriptAudit.CubicSupersingularUnitFrobenius.arithmeticUnit_eq_scalar] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
