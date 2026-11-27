import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassNativeFrobeniusPowers
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace

/-! Native centered Frobenius agrees with the correct power after extending the finite field. -/

namespace ManuscriptAudit.CubicExtensionFrobeniusAt

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicNonsplitThreeAdicTrace TorsionFrobeniusModule WeierstrassNativeFrobeniusPowers

noncomputable section

variable (K E L : Type*) [Field K] [Field E] [Field L]
  [Algebra K L] [Algebra E L] [DecidableEq L]

private theorem pointMapAt_eq_of_scalars (W₀ : Affine K) (W₁ : Affine E) (V : Affine L)
    (h₀ : W₀.baseChange L = V) (h₁ : W₁.baseChange L = V)
    (g₀ : L →ₐ[K] L) (g₁ : L →ₐ[E] L) (h : ∀ x, g₀ x = g₁ x) :
    pointMapAt K L W₀ V h₀ g₀ = pointMapAt E L W₁ V h₁ g₁ := by
  apply AddMonoidHom.ext
  intro P
  cases P with
  | zero =>
    change pointMapAt K L W₀ V h₀ g₀ 0 = pointMapAt E L W₁ V h₁ g₁ 0
    simp only [map_zero]
  | some x y hp =>
    obtain ⟨_, he₀⟩ := pointMapAt_some K L W₀ V h₀ g₀ x y hp
    obtain ⟨_, he₁⟩ := pointMapAt_some E L W₁ V h₁ g₁ x y hp
    rw [he₀, he₁, Affine.Point.some.injEq]
    exact ⟨h x, h y⟩

variable [Fintype K] [Fintype E]

/-- Arithmetic Frobenius on a chosen centered geometric model of the base change. -/
def scalarActionAt (m : ℕ) (a : E) (v : L) (h : algebraMap E L a = v) :
    Module.End (ZMod m) (Torsion m (Curve v).Point) :=
  mapLinear m (pointMapAt E L (Curve a) (Curve v)
    ((centered_baseChange E L a).trans (congrArg Curve h)) (FiniteField.frobeniusAlgHom E L))

/-- This is an equality of the actual torsion operators on the same geometric point group. -/
theorem eq_pow [Algebra K E] [IsAlgClosed L] (m n : ℕ) (A : K)
    (hA : algebraMap E L (algebraMap K E A) = algebraMap K L A)
    (hCard : Fintype.card E = (Fintype.card K) ^ n) :
    scalarActionAt E L m (algebraMap K E A) (algebraMap K L A) hA =
      (mapLinear m (arithmeticPointFrobenius K L A)) ^ n := by
  change _ = (mapLinear m (pointMapAt K L (Curve A) (Curve (algebraMap K L A))
    (centered_baseChange K L A) (FiniteField.frobeniusAlgHom K L))) ^ n
  rw [torsion_point_map_pow]
  unfold scalarActionAt
  apply congrArg (mapLinear m)
  symm
  apply pointMapAt_eq_of_scalars
  intro x
  rw [field_frobenius_power_apply]
  change x ^ ((Fintype.card K) ^ n) = x ^ Fintype.card E
  rw [hCard]

end
end ManuscriptAudit.CubicExtensionFrobeniusAt

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicExtensionFrobeniusAt.eq_pow
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
