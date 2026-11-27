import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace
import PrimalitySheafVerification.ManuscriptAudit.PowerTateAutomorphism

/-! Actual q-Frobenius is an automorphism of the native rank-two 3-adic module. -/

namespace ManuscriptAudit.CubicThreeAdicFrobenius

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace CubicThreeAdicTate
open TorsionFrobeniusModule PowerTorsionTower PowerTateModule PowerTateAutomorphism

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable (E : Type*) [Field E] [Fintype E]
variable (L : Type*) [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

theorem pointMapAt_injective (W : Affine E) (V : Affine L)
    (he : W.baseChange L = V) (g : L →ₐ[E] L) :
    Function.Injective (pointMapAt E L W V he g) := by
  subst V
  change Function.Injective (Affine.Point.map (W' := W) g)
  exact Affine.Point.map_injective (W' := W) g

theorem arithmeticPointFrobenius_injective (A : E) :
    Function.Injective (arithmeticPointFrobenius E L A) :=
  pointMapAt_injective E L (Curve A) (Curve (algebraMap E L A))
    (centered_baseChange E L A) (FiniteField.frobeniusAlgHom E L)

theorem geometric_threePower_card {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) (n : ℕ) :
    Nat.card (PowerTorsion 3 (GeometricPoints E L A) n) = 9 ^ n :=
  affine_threePower_card
    (by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂)
    (by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃)
    ((map_ne_zero (algebraMap E L)).mpr hA) n

def frobenius {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0) :
    Tate 3 (GeometricPoints E L A) ≃ₗ[ℤ_[3]] Tate 3 (GeometricPoints E L A) :=
  mapEquiv 3 (arithmeticPointFrobenius E L A) (arithmeticPointFrobenius_injective E L A)
    fun n => Nat.finite_of_card_ne_zero
      (by rw [geometric_threePower_card E L h₂ h₃ hA n]; positivity)

theorem evaluate_frobenius {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (n : ℕ) (x : Tate 3 (GeometricPoints E L A)) :
    evaluate 3 _ n (frobenius E L h₂ h₃ hA x) =
      mapLinear (3 ^ n) (arithmeticPointFrobenius E L A) (evaluate 3 _ n x) := rfl

end
end ManuscriptAudit.CubicThreeAdicFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeAdicFrobenius.arithmeticPointFrobenius_injective,
      ``ManuscriptAudit.CubicThreeAdicFrobenius.geometric_threePower_card,
      ``ManuscriptAudit.CubicThreeAdicFrobenius.frobenius,
      ``ManuscriptAudit.CubicThreeAdicFrobenius.evaluate_frobenius] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
