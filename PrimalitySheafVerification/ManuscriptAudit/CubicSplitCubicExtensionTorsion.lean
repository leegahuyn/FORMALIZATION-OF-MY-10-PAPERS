import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicExtensionFrobeniusAt
import PrimalitySheafVerification.ManuscriptAudit.CubicQuadraticTwistFixedTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! Rational torsion for the cubic base extension and its quadratic twist. -/

namespace ManuscriptAudit.CubicSplitCubicExtensionTorsion

open FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace CubicExtensionFrobeniusAt
open CubicQuadraticTwistFixedTorsion TorsionFrobeniusModule

noncomputable section

variable (K E L : Type*) [Field K] [Fintype K] [Field E] [Fintype E] [DecidableEq E]
  [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K E] [Algebra K L] [Algebra E L]

private theorem count_at (m : ℕ) (a : E) (v : L) (h : algebraMap E L a = v) :
    Nat.card (Torsion m (Curve a).Point) =
      Nat.card {P : Torsion m (Curve v).Point // scalarActionAt E L m a v h P = P} := by
  subst v
  exact rational_torsion_card E L m a

private theorem twist_count_at (m : ℕ) {a d : E} (v : L) (h : algebraMap E L a = v)
    (ha : a ≠ 0) (hd : ¬ IsSquare d) (hchar : ringChar E ≠ 2)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) v).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L (d ^ 3 * a))).Δ ≠ 0) :
    Nat.card (Torsion m (Curve (d ^ 3 * a)).Point) =
      Nat.card {P : Torsion m (Curve v).Point // -scalarActionAt E L m a v h P = P} := by
  subst v
  exact twist_rational_torsion_card E L m ha hd hchar hq hΔA hΔB

/-- The two actual rational torsion counts are precisely the two sign-fixed counts of
the cubed arithmetic Frobenius of the original finite field. -/
theorem cubic_extension_count_pair (m : ℕ) {A : K} {d : E}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (hd : ¬ IsSquare d)
    (hCompat : algebraMap E L (algebraMap K E A) = algebraMap K L A)
    (hCard : Fintype.card E = (Fintype.card K) ^ 3)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1) :
    let F := (mapLinear m (arithmeticPointFrobenius K L A)) ^ 3
    Nat.card (Torsion m (Curve (algebraMap K E A)).Point) =
      Nat.card {P : Torsion m (GeometricPoints K L A) // F P = P} ∧
    Nat.card (Torsion m (Curve (d ^ 3 * algebraMap K E A)).Point) =
      Nat.card {P : Torsion m (GeometricPoints K L A) // -F P = P} := by
  let a := algebraMap K E A
  let v := algebraMap K L A
  have h₂E : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K E)).mpr h₂
  have hchar : ringChar E ≠ 2 := by
    intro h
    exact h₂E ((ringChar.spec E 2).mpr (by simpa only [h] using (dvd_rfl : (2 : ℕ) ∣ 2)))
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have ha : a ≠ 0 := (map_ne_zero (algebraMap K E)).mpr hA
  have hv : v ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  have hd₀ : d ≠ 0 := fun h => hd (h.symm ▸ IsSquare.zero)
  have hTw : algebraMap E L (d ^ 3 * a) ≠ 0 :=
    (map_ne_zero (algebraMap E L)).mpr (mul_ne_zero (pow_ne_zero _ hd₀) ha)
  have hpow := eq_pow K E L m 3 A hCompat hCard
  dsimp only
  rw [← hpow]
  exact ⟨count_at E L m a v hCompat,
    twist_count_at E L m v hCompat ha hd hchar hq
      (shortCubic_discriminant_ne_zero h₂L h₃L hv)
      (shortCubic_discriminant_ne_zero h₂L h₃L hTw)⟩

end
end ManuscriptAudit.CubicSplitCubicExtensionTorsion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitCubicExtensionTorsion.cubic_extension_count_pair
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
