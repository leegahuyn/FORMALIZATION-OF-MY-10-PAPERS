import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicCertifiedCoordinateSteps
import PrimalitySheafVerification.ManuscriptAudit.CubicCubeRotation

/-! Checked coordinate chains for native centered-cubic point homomorphisms. -/

namespace ManuscriptAudit.CubicCoordinateChain

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicFractionCertificates CubicFractionCoordinateRules CubicCertifiedCoordinateSteps
open Fraction

noncomputable section

inductive Term where
  | identity
  | add (left right : Term)
  | double (term : Term)
  | rotate (term : Term)
  | neg (term : Term)

def Term.hom {G : Type*} [AddCommGroup G] (rotation : AddMonoid.End G) :
    Term → AddMonoid.End G
  | .identity => 1
  | .add f g => f.hom rotation + g.hom rotation
  | .double f => (2 : ℕ) • f.hom rotation
  | .rotate f => rotation * f.hom rotation
  | .neg f => -f.hom rotation

variable {k : Type*} [CommRing k]

/-- Output fractions are indexed by the native point operation certified by the chain. -/
inductive Chain (A z : k) : Term → Fraction k → Fraction k → Type _
  | identity : Chain A z .identity (scalar 1) (scalar 1)
  | double {f : Term} {u v m U V : Fraction k}
      (step : Chain A z f u v)
      (hm : (tangentFraction A u v).CrossEq m)
      (hU : (xFraction A u u m).CrossEq U)
      (hV : (yFraction u v U m).CrossEq V) :
      Chain A z (.double f) U V
  | add {f g : Term} {u₁ v₁ u₂ v₂ m U V : Fraction k}
      (left : Chain A z f u₁ v₁) (right : Chain A z g u₂ v₂)
      (hm : (secantFraction u₁ v₁ u₂ v₂).CrossEq m)
      (hU : (xFraction A u₁ u₂ m).CrossEq U)
      (hV : (yFraction u₁ v₁ U m).CrossEq V) :
      Chain A z (.add f g) U V
  | rotate {f : Term} {u v : Fraction k} (step : Chain A z f u v) :
      Chain A z (.rotate f) (scalar z * u) v
  | neg {f : Term} {u v : Fraction k} (step : Chain A z f u v) :
      Chain A z (.neg f) u (-v)

def Chain.guards {A z : k} : {term : Term} → {u v : Fraction k} → Chain A z term u v → List k[X]
  | _, _, _, .identity => []
  | _, _, _, .double (v := v) (m := m) (U := U) (V := V) step _ _ _ =>
    step.guards ++ [v.num, m.den, U.den, V.den]
  | _, _, _, .add (u₁ := u₁) (u₂ := u₂) (m := m) (U := U) (V := V) left right _ _ _ =>
    left.guards ++ right.guards ++ [(u₁ - u₂).num, m.den, U.den, V.den]
  | _, _, _, .rotate step => step.guards
  | _, _, _, .neg step => step.guards

variable {L : Type*} [Field L] [Algebra k L] [DecidableEq L]

local notation "ι" => algebraMap k L

set_option maxHeartbeats 1600000 in
theorem chain_coordinates {A z : k} {term : Term} {u v : Fraction k}
    (chain : Chain A z term u v) (h₂ : (2 : L) ≠ 0)
    (hz : (ι z) ^ 3 = 1) (hΔ : (shortCubic (0 : L) (ι A)).Δ ≠ 0)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    (hP : (Curve (ι A)).Nonsingular x y)
    (hGuard : ∀ f ∈ chain.guards, f.eval₂ ι (x ^ 3) ≠ 0) :
    u.ValidAt (x ^ 3) ∧ v.ValidAt (x ^ 3) ∧
      ∃ h : (Curve (ι A)).Nonsingular (x * u.evaluate (x ^ 3)) (y * v.evaluate (x ^ 3)),
        term.hom (CubicCubeRotation.rotate (ι z) hz hΔ) (Affine.Point.some x y hP) =
          Affine.Point.some (x * u.evaluate (x ^ 3)) (y * v.evaluate (x ^ 3)) h := by
  let t := x ^ 3
  let r := CubicCubeRotation.rotate (ι z) hz hΔ
  let P : (Curve (ι A)).Point := Affine.Point.some x y hP
  have he := (nonsingular_iff hΔ x y).mp hP
  induction chain with
  | identity =>
    have hj : (scalar (1 : k)).evaluate (x ^ 3) = (1 : L) := by simp
    have hV : (scalar (1 : k)).ValidAt t := valid_polynomial _ _
    refine ⟨hV, hV, by simpa only [hj, mul_one] using hP, ?_⟩
    change Affine.Point.some x y hP = _
    rw [Affine.Point.some.injEq]
    simp only [hj, mul_one, and_self]
  | @double f u v m U V step hm hU hV ih =>
    have hg : ∀ p ∈ step.guards ++ [v.num, m.den, U.den, V.den], p.eval₂ ι t ≠ 0 := hGuard
    obtain ⟨hu, hv, hQ, eQ⟩ := ih (fun p hp => hg p (by simp [hp]))
    have hm₀ : m.ValidAt t := hg _ (by simp)
    have hU₀ : U.ValidAt t := hg _ (by simp)
    have hV₀ : V.ValidAt t := hg _ (by simp)
    have hv₀ : v.evaluate t ≠ 0 := div_ne_zero (hg v.num (by simp)) hv
    obtain ⟨hR, eR⟩ := double_step h₂ hx hy he hu hv hm₀ hU₀ hV₀ hv₀ hm hU hV hQ
    refine ⟨hU₀, hV₀, hR, ?_⟩
    change (2 : ℕ) • f.hom r P = _
    rw [eQ]
    exact eR
  | @add f g u₁ v₁ u₂ v₂ m U V left right hm hU hV ih₁ ih₂ =>
    have hg : ∀ p ∈ left.guards ++ right.guards ++ [(u₁ - u₂).num, m.den, U.den, V.den],
        p.eval₂ ι t ≠ 0 := hGuard
    obtain ⟨hu₁, hv₁, hP₁, eP₁⟩ := ih₁ (fun p hp => hg p (by simp [hp]))
    obtain ⟨hu₂, hv₂, hP₂, eP₂⟩ := ih₂ (fun p hp => hg p (by simp [hp]))
    have hm₀ : m.ValidAt t := hg _ (by simp)
    have hU₀ : U.ValidAt t := hg _ (by simp)
    have hV₀ : V.ValidAt t := hg _ (by simp)
    have hne : u₁.evaluate t ≠ u₂.evaluate t := by
      intro h
      have hZ : (u₁ - u₂).evaluate t = 0 := by rw [evaluate_sub hu₁ hu₂, h, sub_self]
      exact (div_ne_zero (hg (u₁ - u₂).num (by simp)) (valid_sub hu₁ hu₂)) hZ
    obtain ⟨hR, eR⟩ := add_step hx he hu₁ hv₁ hu₂ hv₂ hm₀ hU₀ hV₀ hne hm hU hV hP₁ hP₂
    refine ⟨hU₀, hV₀, hR, ?_⟩
    change f.hom r P + g.hom r P = _
    rw [eP₁, eP₂]
    exact eR
  | @rotate f u v step ih =>
    obtain ⟨hu, hv, hQ, eQ⟩ := ih hGuard
    have hu' : (scalar z * u).ValidAt t := valid_mul (valid_polynomial _ _) hu
    have hX : x * (scalar z * u).evaluate (x ^ 3) = ι z * (x * u.evaluate (x ^ 3)) := by
      rw [evaluate_mul, evaluate_scalar]
      ring
    have hR : (Curve (ι A)).Nonsingular (ι z * (x * u.evaluate t)) (y * v.evaluate t) := by
      exact ((nonsingular_iff hΔ _ _).mpr (by
        rw [mul_pow (ι z) (x * u.evaluate t) 3, hz, one_mul]
        exact (nonsingular_iff hΔ _ _).mp hQ))
    have hNew : (Curve (ι A)).Nonsingular (x * (scalar z * u).evaluate (x ^ 3))
        (y * v.evaluate (x ^ 3)) := by
      rw [hX]
      exact hR
    refine ⟨hu', hv, hNew, ?_⟩
    change r (f.hom r P) = _
    rw [eQ, CubicCubeRotation.rotate_some, Affine.Point.some.injEq]
    exact ⟨hX.symm, rfl⟩
  | @neg f u v step ih =>
    obtain ⟨hu, hv, hQ, eQ⟩ := ih hGuard
    have hv' : (-v).ValidAt t := hv
    have hY : (Curve (ι A)).negY (x * u.evaluate (x ^ 3)) (y * v.evaluate (x ^ 3)) =
        y * (-v).evaluate (x ^ 3) := by
      rw [CubicTriplingCoordinates.negY_eq, evaluate_neg]
      ring
    have hR := (Affine.nonsingular_neg ..).mpr hQ
    have hNew : (Curve (ι A)).Nonsingular (x * u.evaluate (x ^ 3))
        (y * (-v).evaluate (x ^ 3)) := hY ▸ hR
    refine ⟨hu, hv', hNew, ?_⟩
    change -(f.hom r P) = _
    rw [eQ, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, hY⟩

end
end ManuscriptAudit.CubicCoordinateChain

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicCoordinateChain.chain_coordinates
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
