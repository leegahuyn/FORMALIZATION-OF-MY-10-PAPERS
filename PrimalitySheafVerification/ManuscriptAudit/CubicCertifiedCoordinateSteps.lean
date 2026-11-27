import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFractionCoordinateRules

/-! A checked rational certificate step computes the actual centered cubic point operation. -/

namespace ManuscriptAudit.CubicCertifiedCoordinateSteps

open WeierstrassCurve CubicThreeTorsionOrdinate
open CubicFractionCertificates CubicFractionCoordinateRules CubicNormalizedCoordinates
open Fraction

variable {k L : Type*} [CommRing k] [Field L] [Algebra k L] [DecidableEq L]
variable {A : k} {x y : L} {u₁ v₁ u₂ v₂ m u₃ v₃ : Fraction k}

local notation "t" => x ^ 3
local notation "a" => algebraMap k L A

set_option maxHeartbeats 800000 in
theorem add_step (hx : x ≠ 0) (he : y ^ 2 = t + a)
    (hu₁ : u₁.ValidAt t) (hv₁ : v₁.ValidAt t) (hu₂ : u₂.ValidAt t) (hv₂ : v₂.ValidAt t)
    (hm : m.ValidAt t) (hu₃ : u₃.ValidAt t) (hv₃ : v₃.ValidAt t)
    (hne : u₁.evaluate t ≠ u₂.evaluate t)
    (hcm : (secantFraction u₁ v₁ u₂ v₂).CrossEq m)
    (hcx : (xFraction A u₁ u₂ m).CrossEq u₃) (hcy : (yFraction u₁ v₁ u₃ m).CrossEq v₃)
    (h₁ : (Curve a).Nonsingular (x * u₁.evaluate t) (y * v₁.evaluate t))
    (h₂ : (Curve a).Nonsingular (x * u₂.evaluate t) (y * v₂.evaluate t)) :
    ∃ h₃ : (Curve a).Nonsingular (x * u₃.evaluate t) (y * v₃.evaluate t),
      (Affine.Point.some (x * u₁.evaluate t) (y * v₁.evaluate t) h₁ : (Curve a).Point) +
        Affine.Point.some (x * u₂.evaluate t) (y * v₂.evaluate t) h₂ =
      Affine.Point.some (x * u₃.evaluate t) (y * v₃.evaluate t) h₃ := by
  obtain ⟨hm₀, em⟩ := secant_check hu₁ hv₁ hu₂ hv₂ hne
  obtain ⟨hU₀, eU⟩ := x_check (A := A) (pow_ne_zero 3 hx) hu₁ hu₂ hm
  obtain ⟨hV₀, eV⟩ := y_check hu₁ hv₁ hu₃ hm
  have hM := (value_eq hm₀ hm hcm).symm.trans em
  have hX := (value_eq hU₀ hu₃ hcx).symm.trans eU
  have hY := (value_eq hV₀ hv₃ hcy).symm.trans eV
  rw [hM] at hX
  rw [hM, hX] at hY
  obtain ⟨hQ, eQ⟩ := add_of_abscissa_ne hx he hne h₁ h₂
  have hNew : (Curve a).Nonsingular (x * u₃.evaluate t) (y * v₃.evaluate t) := by
    have hOld := hQ
    rw [← hY, ← hX] at hOld
    exact hOld
  refine ⟨hNew, eQ.trans ?_⟩
  rw [Affine.Point.some.injEq]
  exact ⟨congrArg (fun z : L => x * z) hX.symm, congrArg (fun z : L => y * z) hY.symm⟩

set_option maxHeartbeats 800000 in
theorem double_step (h₂ : (2 : L) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (he : y ^ 2 = t + a)
    (hu₁ : u₁.ValidAt t) (hv₁ : v₁.ValidAt t)
    (hm : m.ValidAt t) (hu₃ : u₃.ValidAt t) (hv₃ : v₃.ValidAt t)
    (hv : v₁.evaluate t ≠ 0)
    (hcm : (tangentFraction A u₁ v₁).CrossEq m)
    (hcx : (xFraction A u₁ u₁ m).CrossEq u₃) (hcy : (yFraction u₁ v₁ u₃ m).CrossEq v₃)
    (h₁ : (Curve a).Nonsingular (x * u₁.evaluate t) (y * v₁.evaluate t)) :
    ∃ h₃ : (Curve a).Nonsingular (x * u₃.evaluate t) (y * v₃.evaluate t),
      (2 : ℕ) • (Affine.Point.some (x * u₁.evaluate t) (y * v₁.evaluate t) h₁ : (Curve a).Point) =
        Affine.Point.some (x * u₃.evaluate t) (y * v₃.evaluate t) h₃ := by
  have hs : t + a ≠ 0 := he ▸ pow_ne_zero 2 hy
  obtain ⟨hm₀, em⟩ := tangent_check hu₁ h₂ hs hv
  obtain ⟨hU₀, eU⟩ := x_check (A := A) (pow_ne_zero 3 hx) hu₁ hu₁ hm
  obtain ⟨hV₀, eV⟩ := y_check hu₁ hv₁ hu₃ hm
  have hM := (value_eq hm₀ hm hcm).symm.trans em
  have hX := (value_eq hU₀ hu₃ hcx).symm.trans eU
  have hY := (value_eq hV₀ hv₃ hcy).symm.trans eV
  rw [hM] at hX
  rw [hM, hX] at hY
  obtain ⟨hQ, eQ⟩ := double_some h₂ hx hy he hv h₁
  have hNew : (Curve a).Nonsingular (x * u₃.evaluate t) (y * v₃.evaluate t) := by
    have hOld := hQ
    rw [← hY, ← hX] at hOld
    exact hOld
  refine ⟨hNew, eQ.trans ?_⟩
  rw [Affine.Point.some.injEq]
  exact ⟨congrArg (fun z : L => x * z) hX.symm, congrArg (fun z : L => y * z) hY.symm⟩

end ManuscriptAudit.CubicCertifiedCoordinateSteps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCertifiedCoordinateSteps.add_step,
      ``ManuscriptAudit.CubicCertifiedCoordinateSteps.double_step] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
