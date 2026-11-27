import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicSignedTwistRotation
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicTateRotationCoefficients

/-! Native Tate coefficients for every sign and cubic rotation of an actual sextic twist. -/

namespace ManuscriptAudit.CubicSignedTwistTate

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicFrobeniusSexticTwists CubicOrdinatePreservingTwist CubicRotationCombination
open CubicSignedTwistRotation PowerTateModule

noncomputable section

set_option maxHeartbeats 800000

def signedCoefficients (n : Fin 3) (ε a b : ℤ) : ℤ × ℤ :=
  (ε * (rotatedCoefficients n a b).1, ε * (rotatedCoefficients n a b).2)

/-- Both sign choices and all three rotations preserve the integral norm. -/
theorem signedCoefficients_norm (n : Fin 3) (ε a b : ℤ) (hε : ε = 1 ∨ ε = -1) :
    let c := (signedCoefficients n ε a b).1
    let d := (signedCoefficients n ε a b).2
    c ^ 2 - c * d + d ^ 2 = a ^ 2 - a * b + b ^ 2 := by
  have hS : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> decide
  let c := (rotatedCoefficients n a b).1
  let d := (rotatedCoefficients n a b).2
  change (ε * c) ^ 2 - (ε * c) * (ε * d) + (ε * d) ^ 2 = _
  calc
    _ = ε ^ 2 * (c ^ 2 - c * d + d ^ 2) := by ring
    _ = a ^ 2 - a * b + b ^ 2 := by
      rw [hS, one_mul]
      fin_cases n
      · rfl
      · change (-b) ^ 2 - (-b) * (a - b) + (a - b) ^ 2 = _
        ring
      · change (b - a) ^ 2 - (b - a) * (-a) + (-a) ^ 2 = _
        ring

variable {E L : Type*} [Field E] [Fintype E] [Field L] [Algebra E L]
    [IsAlgClosed L] [DecidableEq L]

/-- The signed rotation computes exact trace and determinant on the target's actual Tate module. -/
theorem trace_det (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) (A B : E)
    (hA : A ≠ 0) (hB : B ≠ 0) {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L B)).Δ ≠ 0)
    (z : L) (hz : z ^ 3 = 1) (hz₁ : z ≠ 1)
    (n : Fin 3) (hX : (algebraMap E L (parameter A B k)) ^ 2 = z ^ n.val)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hY : (algebraMap E L (parameter A B k)) ^ 3 = (ε : L))
    (a b : ℤ)
    (hF : arithmeticFrobenius E L A =
      a • (1 : AddMonoid.End (Geometric E L A)) +
        b • (pointRotation hz hΔA : AddMonoid.End (Geometric E L A)))
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let c := (signedCoefficients n ε a b).1
    let d := (signedCoefficients n ε a b).2
    LinearMap.trace ℤ_[l] (Tate l (Geometric E L B))
      (endMap l (arithmeticFrobenius E L B)) = ((2 * c - d : ℤ) : ℤ_[l]) ∧
    LinearMap.det (endMap l (arithmeticFrobenius E L B)) =
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℤ_[l]) := by
  let r : AddMonoid.End (Geometric E L A) := pointRotation hz hΔA
  have h₀ : algebraMap E L A ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  have hr : r ^ 2 + r + (1 : AddMonoid.End (Geometric E L A)) = 0 := by
    apply AddMonoidHom.ext
    intro P
    change r (r P) + r P + P = 0
    exact CubicRotationQuadratic.rotate_sum_eq_zero h₂ h₃ h₀ hz hz₁ hΔA P
  let F := ε • (r ^ n.val * arithmeticFrobenius E L A)
  let c := (signedCoefficients n ε a b).1
  let d := (signedCoefficients n ε a b).2
  have hRot : r ^ n.val * arithmeticFrobenius E L A =
      (rotatedCoefficients n a b).1 • (1 : AddMonoid.End (Geometric E L A)) +
        (rotatedCoefficients n a b).2 • r := by
    rw [hF]
    exact rotation_pow_linear r hr n a b
  have hComb : F = c • (1 : AddMonoid.End (Geometric E L A)) + d • r := by
    change ε • (r ^ n.val * arithmeticFrobenius E L A) = _
    rw [hRot, smul_add, smul_smul, smul_smul] <;> rfl
  obtain ⟨ht, hd⟩ := CubicTateRotationCoefficients.trace_det h₂ h₃ h₀ hz hz₁ hΔA
    l hl F c d hComb
  rw [signedCoefficients_norm n ε a b hε] at hd
  obtain ⟨e, he⟩ := frobenius_conjugate_signed_pow (E := E) (L := L) (A := A) (B := B)
    hA hB hq hΔA hΔB hz n.val hX ε hε hY
  let T := mapAddEquiv l e
  let G := endMap l (arithmeticFrobenius E L B)
  have h (v : Tate l (Geometric E L A)) : G (T v) = T (endMap l F v) := by
    apply PowerTateModule.ext l (Geometric E L B)
    intro j
    apply Subtype.ext
    exact he (evaluate l (Geometric E L A) j v : Geometric E L A)
  have hConj : T.conj (endMap l F) = G := by
    apply LinearMap.ext
    intro x
    change T (endMap l F (T.symm x)) = G x
    rw [← h, T.apply_symm_apply]
  change LinearMap.trace ℤ_[l] (Tate l (Geometric E L B)) G = ((2 * c - d : ℤ) : ℤ_[l]) ∧
    LinearMap.det G = ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℤ_[l])
  rw [← hConj]
  refine ⟨(LinearMap.trace_conj' _ _).trans ht, ?_⟩
  have hMap : T.conj (endMap l F) = T.toLinearMap ∘ₗ (endMap l F) ∘ₗ T.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    rfl
  rw [hMap]
  exact (LinearMap.det_conj (endMap l F) T).trans hd

end
end ManuscriptAudit.CubicSignedTwistTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSignedTwistTate.signedCoefficients_norm,
      ``ManuscriptAudit.CubicSignedTwistTate.trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
