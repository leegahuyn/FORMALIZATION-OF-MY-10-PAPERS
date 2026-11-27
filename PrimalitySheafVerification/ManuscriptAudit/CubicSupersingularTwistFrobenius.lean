import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusScaling
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularUnitFrobenius

/-! Genuine arithmetic Frobenius on each centered sextic twist. -/

namespace ManuscriptAudit.CubicSupersingularTwistFrobenius

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace CubicSupersingularUnitFrobenius CubicFrobeniusScaling
open CubicPointScaling

noncomputable section

variable (L : Type*) [Field L] [DecidableEq L]

theorem sixth_root_nonzero {v : L} (hv : v ^ 6 = 1) : v ≠ 0 := by
  intro he
  rw [he, zero_pow (by decide : (6 : ℕ) ≠ 0)] at hv
  exact zero_ne_one hv

def sexticScale {v : L} (hv : v ^ 6 = 1) (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) :
    AddMonoid.End (UnitPoints L) :=
  scale (sixth_root_nonzero L hv) (show v ^ 6 * (1 : L) = 1 by rw [hv, one_mul]) hΔ

variable (E : Type*) [Field E] [Fintype E] [Algebra E L] [IsAlgClosed L]

/-- Scaling by a sixth root of the coefficient conjugates Frobenius to a
sixth-root scaling followed by the reference Frobenius. -/
theorem exists_twist_conjugacy {A : E} (hA : A ≠ 0) (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0) :
    ∃ (v : L) (hv : v ^ 6 = 1) (e : UnitPoints L ≃+ GeometricPoints E L A),
      ∀ P, arithmeticPointFrobenius E L A (e P) =
        e (sexticScale L hv hΔ (arithmeticUnit E L P)) := by
  let a := algebraMap E L A
  have ha : a ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < (6 : ℕ))
  have hu₀ : u ≠ 0 := by
    intro he
    exact ha (by simpa [he] using hu.symm)
  have hUA : u ^ 6 * (1 : L) = a := by simpa only [mul_one] using hu
  let g := FiniteField.frobeniusAlgHom E L
  let v := g u / u
  have hGu : g u = u * v := by
    change g u = u * (g u / u)
    rw [mul_comm u, div_mul_cancel₀ (g u) hu₀]
  have hGp : (g u) ^ 6 = u ^ 6 := by
    calc
      (g u) ^ 6 = g (u ^ 6) := (map_pow g u 6).symm
      _ = g a := congrArg g hu
      _ = a := g.commutes A
      _ = u ^ 6 := hu.symm
  have hv : v ^ 6 = 1 := by
    change (g u / u) ^ 6 = 1
    rw [div_pow, hGp, div_self (pow_ne_zero _ hu₀)]
  let e := scaleEquiv hu₀ hUA hΔ hΔA
  refine ⟨v, hv, e, ?_⟩
  intro P
  change nativeMap E L g A (e P) = e (sexticScale L hv hΔ (unitMap E L g P))
  cases P with
  | zero =>
    change nativeMap E L g A (e 0) = e (sexticScale L hv hΔ (unitMap E L g 0))
    simp only [map_zero]
  | some x y h =>
    obtain ⟨h₁, e₁⟩ := unitMap_some E L g h
    obtain ⟨h₂, e₂⟩ := nativeMap_some E L g A (scaled_nonsingular hUA hΔA h)
    dsimp only [e, sexticScale]
    rw [scaleEquiv_some hu₀ hUA hΔ hΔA h, e₁, e₂, scale_some, scaleEquiv_some,
      Affine.Point.some.injEq]
    constructor
    · rw [map_mul, map_pow, hGu]
      ring
    · rw [map_mul, map_pow, hGu]
      ring

end
end ManuscriptAudit.CubicSupersingularTwistFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularTwistFrobenius.exists_twist_conjugacy
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
