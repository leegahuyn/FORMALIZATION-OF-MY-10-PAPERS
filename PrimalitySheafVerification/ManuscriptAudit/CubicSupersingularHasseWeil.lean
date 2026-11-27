import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularPointCountRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualHasseWeil

/-! Actual Hasse–Weil zeta series over an arbitrary finite supersingular base. -/

namespace ManuscriptAudit.CubicSupersingularHasseWeil

open WeierstrassCurve FiniteFieldPointCount
open PointCountExponential PowerSeries Paper5ExtensionRecurrence
open CubicSupersingularPointCountRecurrence

noncomputable section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
variable (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, DecidableEq (E n)]
variable [∀ n, Algebra F (E n)]

def counts (A : F) : ℂ⟦X⟧ :=
  X * PowerSeries.mk fun n =>
    (Nat.card (shortCubic (0 : E n) (algebraMap F (E n) A)).toProjective.Point : ℂ)

variable (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] [CharP F p]
variable [∀ n, Algebra (ZMod p) (E n)] [∀ n, CharP (E n) p]
variable [∀ n, IsScalarTower (ZMod p) F (E n)]

theorem counts_eq_two_roots (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    [Algebra F L] [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]
    [∀ n, Algebra (E n) L] [∀ n, IsScalarTower F (E n) L]
    (hp : 5 ≤ p) (hP : p % 3 = 2)
    (hDegree : ∀ n, Module.finrank F (E n) = n + 1)
    {A : F} (hA : A ≠ 0) {α β : ℂ}
    (hSum : α + β = (signedCount F A : ℂ)) (hProd : α * β = (Fintype.card F : ℂ)) :
    counts F E A = twoRootCounts (Fintype.card F : ℂ) α β := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [counts, twoRootCounts, coeff_zero_X_mul]
  | succ n =>
    simp only [counts, twoRootCounts, coeff_succ_X_mul, coeff_mk]
    have hc : Fintype.card (E n) = Fintype.card F ^ (n + 1) := by
      rw [Module.card_eq_pow_finrank (K := F) (V := E n), hDegree n]
    have ht := signed_count_eq_recurrence p F (E n) L hp hP hA
    rw [signedCount, hc, hDegree n] at ht
    have ht' := congrArg (fun t : ℤ => (t : ℂ)) ht
    push_cast at ht'
    change (Fintype.card F : ℂ) ^ (n + 1) + 1 -
        (Nat.card (shortCubic (0 : E n) (algebraMap F (E n) A)).toProjective.Point : ℂ) =
      (Paper5PrintedRecurrence.recurrence (Fintype.card F) (signedCount F A) (n + 1) : ℂ) at ht'
    rw [recurrence_cast_eq_root_powers (Fintype.card F) (signedCount F A) α β hSum hProd] at ht'
    linear_combination -ht'

theorem zeta_eq (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    [Algebra F L] [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]
    [∀ n, Algebra (E n) L] [∀ n, IsScalarTower F (E n) L]
    (hp : 5 ≤ p) (hP : p % 3 = 2)
    (hDegree : ∀ n, Module.finrank F (E n) = n + 1) {A : F} (hA : A ≠ 0) :
    zetaOfCountSeries (counts F E A) =
      (1 - X * C (signedCount F A : ℂ) + X ^ 2 * C (Fintype.card F : ℂ)) *
        ((1 - X)⁻¹ * (1 - X * C (Fintype.card F : ℂ))⁻¹) := by
  obtain ⟨α, β, hSum, hProd⟩ :=
    Paper5ActualHasseWeil.exist_two_roots (signedCount F A : ℂ) (Fintype.card F : ℂ)
  rw [counts_eq_two_roots F E p L hp hP hDegree hA hSum hProd, twoRootCounts_zeta,
    geometric_eq_inv (1 : ℂ), geometric_eq_inv (Fintype.card F : ℂ)]
  have hs : C α + C β = C (signedCount F A : ℂ) := by rw [← map_add, hSum]
  have hp' : C α * C β = C (Fintype.card F : ℂ) := by rw [← map_mul, hProd]
  have hF : linearFactor α * linearFactor β =
      (1 - X * C (signedCount F A : ℂ) + X ^ 2 * C (Fintype.card F : ℂ)) := by
    unfold linearFactor
    linear_combination -(X : ℂ⟦X⟧) * hs + X ^ 2 * hp'
  rw [hF]
  simp [linearFactor]

end
end ManuscriptAudit.CubicSupersingularHasseWeil

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSupersingularHasseWeil.counts_eq_two_roots,
      ``ManuscriptAudit.CubicSupersingularHasseWeil.zeta_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
