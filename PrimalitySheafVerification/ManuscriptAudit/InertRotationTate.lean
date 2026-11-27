import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.EisensteinNormInert
import PrimalitySheafVerification.ManuscriptAudit.RotationNormUnit
import PrimalitySheafVerification.ManuscriptAudit.CubicTateRotationCoefficients

/-! On a rank-two Tate module the cubic rotation remains nonscalar at every inert prime. -/

namespace ManuscriptAudit.InertRotationTate

open Module PowerTorsionTower TorsionFrobeniusModule PowerTateModule PowerTateRankTwo
open PowerTateEvaluationSurjective RotationNormUnit EisensteinNormInert

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]
variable (B : Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l G 1))
variable (hDiv : Function.Surjective (fun P : G => l • P))

/-- The native Tate basis obtained from the first torsion level. -/
def basis : Basis (Fin 2) ℤ_[l] (Tate l G) :=
  (Basis.finTwoProd ℤ_[l]).map (padicPairEquiv l G B hDiv)

include B hDiv in
theorem rotation_not_scalar (hl : l % 3 = 2) (r : AddMonoid.End G)
    (hr : r ^ 2 + r + 1 = 0) :
    ¬ ∃ c : ℤ_[l], endMap l r = c • (1 : Module.End ℤ_[l] (Tate l G)) := by
  rintro ⟨c, hc⟩
  letI : Fact (Nat.Prime (l ^ 1)) := ⟨by simpa only [pow_one] using (Fact.out : Nat.Prime l)⟩
  let z := PadicInt.toZModPow 1 c
  let S := mapLinear (l ^ 1) r
  have hS : S ^ 2 + S + 1 = 0 := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    exact congrArg (fun f : AddMonoid.End G => f P.val) hr
  have hR : S = z • (1 : Module.End (ZMod (l ^ 1)) (PowerTorsion l G 1)) :=
    scalar_reduction l G B hDiv r c hc 1
  rw [hR] at hS
  have he := congrArg (fun f : Module.End (ZMod (l ^ 1)) (PowerTorsion l G 1) => f (B 0)) hS
  change z • (z • B 0) + z • B 0 + B 0 = 0 at he
  have hZ : (z ^ 2 + z + 1) • B 0 = 0 := by
    calc
      _ = z • (z • B 0) + z • B 0 + B 0 := by
        rw [add_smul, add_smul, one_smul, pow_two, mul_smul]
      _ = _ := he
  have hz : z ^ 2 + z + 1 = 0 := (smul_eq_zero.mp hZ).resolve_right (B.ne_zero 0)
  have hInert : (l ^ 1) % 3 = 2 := by simpa only [pow_one] using hl
  have hh := norm_ne_zero (l ^ 1) hInert (a := z) (b := -1)
    (Or.inr (neg_ne_zero.mpr one_ne_zero))
  apply hh
  convert hz using 1 <;> ring

include B hDiv in
/-- The exact native trace and determinant are the integral Eisenstein trace and norm. -/
theorem trace_det (hl : l % 3 = 2) (r F : AddMonoid.End G)
    (hr : r ^ 2 + r + 1 = 0) (a b : ℤ) (hF : F = combination r a b) :
    LinearMap.trace ℤ_[l] (Tate l G) (endMap l F) = ((2 * a - b : ℤ) : ℤ_[l]) ∧
      LinearMap.det (endMap l F) = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℤ_[l]) := by
  let S := endMap l r
  have hN := rotation_not_scalar l G B hDiv hl r hr
  have hS : S ^ 2 + S + 1 = 0 := by
    simpa only [S, map_pow, map_add, map_one, map_zero] using congrArg (endMap l) hr
  let J : Module.End ℤ_[l] (Tate l G) := 1
  have hComb : endMap l F = (a : ℤ_[l]) • J + (b : ℤ_[l]) • S := by
    have he := congrArg (endMap l) hF
    change endMap l F = endMap l (a • (1 : AddMonoid.End G) + b • r) at he
    rw [map_add, map_zsmul, map_zsmul, map_one,
      ← Int.cast_smul_eq_zsmul ℤ_[l] a J, ← Int.cast_smul_eq_zsmul ℤ_[l] b S] at he
    exact he
  rw [hComb]
  simpa only [J, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using
    CubicTateRotationCoefficients.trace_det_linear (basis l G B hDiv) S hN hS
      (a : ℤ_[l]) (b : ℤ_[l])

end
end ManuscriptAudit.InertRotationTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.InertRotationTate.rotation_not_scalar,
      ``ManuscriptAudit.InertRotationTate.trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
