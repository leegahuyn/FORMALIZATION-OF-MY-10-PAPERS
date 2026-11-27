import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusScaling
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenRotation

/-! The actual Frobenius of the printed y²=x³+1 row at p=7, via the ordinary twist. -/

namespace ManuscriptAudit.Paper5OrdinarySevenOneTwist

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicPointScaling CubicFrobeniusScaling CubicNonsplitFrobeniusTrace
open Paper5OrdinarySeven Paper5OrdinarySevenGeometry Paper5OrdinarySevenFrobenius
open Paper5OrdinarySevenRotation

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]

private abbrev W := (ordinaryCurve L).toAffine
private abbrev a (A : ZMod 7) := algebraMap (ZMod 7) L A
private abbrev g := FiniteField.frobeniusAlgHom (ZMod 7) L

private def transport {U V : Affine L} (h : U = V) : U.Point ≃+ V.Point := by
  subst V
  exact AddEquiv.refl _

private theorem transport_some {U V : Affine L} (h : U = V) {x y : L}
    (hP : U.Nonsingular x y) :
    transport L h (Affine.Point.some x y hP) =
      Affine.Point.some x y (h ▸ hP) := by
  subst V
  rfl

private theorem ordinary_curve_eq : W L = Curve (a L 5) := by
  simpa only [map_ofNat] using ordinary_eq_centered L

def ordinaryEquiv : Points L ≃+ (Curve (a L 5)).Point :=
  transport L (ordinary_curve_eq L)

theorem ordinaryEquiv_some {x y : L} (h : (W L).Nonsingular x y) :
    ordinaryEquiv L (Affine.Point.some x y h) =
      Affine.Point.some x y (ordinary_curve_eq L ▸ h) :=
  transport_some L (ordinary_curve_eq L) h

theorem disc (A : ZMod 7) (hA : A ≠ 0) :
    (shortCubic (0 : L) (a L A)).Δ ≠ 0 :=
  CubicThreeTorsionCard.shortCubic_discriminant_ne_zero Paper5OrdinarySevenSecant.two_ne (three_ne L)
    ((map_ne_zero (algebraMap (ZMod 7) L)).mpr hA)

theorem equiv_frobenius (P : Points L) :
    nativeMap (ZMod 7) L (g L) 5 (ordinaryEquiv L P) =
      ordinaryEquiv L (nativeFrobenius L P) := by
  cases P with
  | zero =>
    change nativeMap (ZMod 7) L (g L) 5 (ordinaryEquiv L 0) =
      ordinaryEquiv L (nativeFrobenius L 0)
    simp only [map_zero]
  | some x y h =>
    obtain ⟨hF, eF⟩ := pointMapAt_some (ZMod 7) L (ordinaryCurve (ZMod 7)).toAffine
      (W L) (ordinary_baseChange L) (g L) x y h
    change nativeFrobenius L (Affine.Point.some x y h) = _ at eF
    have h' : (Curve (a L 5)).Nonsingular x y :=
      Eq.mp (congrArg (fun V : Affine L => V.Nonsingular x y) (ordinary_curve_eq L)) h
    obtain ⟨hG, eG⟩ := nativeMap_some (ZMod 7) L (g L) 5 h'
    rw [ordinaryEquiv_some L h, eG, eF, ordinaryEquiv_some]

private theorem v_ne_zero : (3 : L) ≠ 0 := three_ne L

private theorem v_pow_mul : (3 : L) ^ 6 * a L 5 = a L 5 := by
  simp only [map_ofNat]
  linear_combination (520 : L) * seven_zero L

private theorem twist_rotation (P : Points L) :
    scale (v_ne_zero L) (v_pow_mul L) (disc L 5 (by decide)) (ordinaryEquiv L P) =
      ordinaryEquiv L (-rotation L P) := by
  cases P with
  | zero =>
    change scale (v_ne_zero L) (v_pow_mul L) (disc L 5 (by decide)) (ordinaryEquiv L 0) =
      ordinaryEquiv L (-rotation L 0)
    simp only [map_zero, neg_zero]
  | some x y h =>
    rw [ordinaryEquiv_some L h, scale_some, rotation_some, Affine.Point.neg_some,
      ordinaryEquiv_some, Affine.Point.some.injEq, negY_eq]
    exact ⟨by linear_combination x * seven_zero L, by linear_combination (4 * y) * seven_zero L⟩

private theorem twisted_frobenius (P : Points L) :
    -rotation L (nativeFrobenius L P) = -((3 : ℕ) • P) - (2 : ℕ) • rotation L P := by
  have hF : nativeFrobenius L P = -P - (3 : ℕ) • rotation L P :=
    congrArg (fun m : AddMonoid.End (Points L) => m P) (native_eq_rotation L)
  have hR : rotation L (rotation L P) = -P - rotation L P := by
    calc
      _ = (rotation L P + rotation L (rotation L P)) - rotation L P := by abel
      _ = _ := by rw [rotation_sum]
  rw [hF, map_sub, map_neg, map_nsmul, hR]
  abel

/-- The actual y²=x³+1 map is conjugate to −3−2ρ on the ordinary reference twist. -/
theorem exists_frobenius_conjugacy :
    ∃ e : Points L ≃+ (Curve (a L 1)).Point, ∀ P : Points L,
      nativeMap (ZMod 7) L (g L) 1 (e P) =
        e (-((3 : ℕ) • P) - (2 : ℕ) • rotation L P) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (3 : L) (by decide : 0 < (6 : ℕ))
  have hu₀ : u ≠ 0 := by
    intro he
    exact v_ne_zero L (by simpa [he] using hu.symm)
  have hAB : u ^ 6 * a L 5 = a L 1 := by
    rw [hu]
    simp only [map_ofNat, map_one]
    linear_combination (2 : L) * seven_zero L
  have hgu : g L u = u * 3 := by
    change u ^ Fintype.card (ZMod 7) = _
    rw [ZMod.card, show (7 : ℕ) = 6 + 1 by decide, pow_add, pow_one, hu, mul_comm]
  let e₀ := ordinaryEquiv L
  let e₁ := scaleEquiv hu₀ hAB (disc L 5 (by decide)) (disc L 1 one_ne_zero)
  refine ⟨e₀.trans e₁, fun P => ?_⟩
  change nativeMap (ZMod 7) L (g L) 1 (e₁ (e₀ P)) =
    e₁ (e₀ (-((3 : ℕ) • P) - (2 : ℕ) • rotation L P))
  have h := nativeMap_scale (g L) hu₀ (v_ne_zero L) hAB (v_pow_mul L)
    (disc L 5 (by decide)) (disc L 1 one_ne_zero) hgu (e₀ P)
  change nativeMap (ZMod 7) L (g L) 1 (e₁ (e₀ P)) =
    e₁ (scale (v_ne_zero L) (v_pow_mul L) (disc L 5 (by decide))
      (nativeMap (ZMod 7) L (g L) 5 (ordinaryEquiv L P))) at h
  rw [equiv_frobenius, twist_rotation, twisted_frobenius] at h
  exact h

end
end ManuscriptAudit.Paper5OrdinarySevenOneTwist

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySevenOneTwist.exists_frobenius_conjugacy
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
