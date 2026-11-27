import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Polynomial.Basic
import PrimalitySheafVerification.ManuscriptAudit.PointCountExponential
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedActualExtensionCounts

/-! The local Hasse–Weil function built from all actual good-reduction point counts. -/

namespace ManuscriptAudit.Paper5ActualHasseWeil

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open Paper5ExtensionRecurrence Paper5PrintedActualExtensionCounts
open PointCountExponential PowerSeries

noncomputable section

private abbrev Series := ℂ⟦X⟧

def firstTrace (p : ℕ) [Fact p.Prime] (A : ZMod p) : ℤ :=
  (p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ)

def actualCounts (p : ℕ) [Fact p.Prime] (A : ZMod p) : Series :=
  X * PowerSeries.mk fun n =>
    (Nat.card ((paper5TraceCurve p A).baseChange (GaloisField p (n + 1))).toProjective.Point : ℂ)

def actualZeta (p : ℕ) [Fact p.Prime] (A : ZMod p) : Series :=
  zetaOfCountSeries (actualCounts p A)

theorem exist_two_roots (a q : ℂ) :
    ∃ α β : ℂ, α + β = a ∧ α * β = q := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (a ^ 2 - 4 * q) zero_lt_two
  refine ⟨(a + d) / 2, (a - d) / 2, by ring, ?_⟩
  linear_combination -(1 / 4 : ℂ) * hd

theorem actualCounts_eq (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) (α β : ℂ)
    (ha : α + β = (firstTrace p A : ℂ)) (hm : α * β = (p : ℂ)) :
    actualCounts p A = twoRootCounts (p : ℂ) α β := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [actualCounts, twoRootCounts, coeff_zero_X_mul]
  | succ n =>
    simp only [actualCounts, twoRootCounts, coeff_succ_X_mul, coeff_mk]
    classical
    let F := GaloisField p (n + 1)
    letI : Fintype F := Fintype.ofFinite F
    have hd : Module.finrank (ZMod p) F = n + 1 := GaloisField.finrank p n.succ_ne_zero
    have hcard : Fintype.card F = p ^ (n + 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p (n + 1) n.succ_ne_zero
    have ht := Paper5PrintedActualExtensionCounts.actual_extension_trace_eq_recurrence (E := F) hp hA
    rw [hcard, hd] at ht
    have ht' := congrArg (fun x : ℤ => (x : ℂ)) ht
    push_cast at ht'
    change (p : ℂ) ^ (n + 1) + 1 -
        (Nat.card ((paper5TraceCurve p A).baseChange F).toProjective.Point : ℂ) =
      (Paper5PrintedRecurrence.recurrence p (firstTrace p A) (n + 1) : ℂ) at ht'
    rw [recurrence_cast_eq_root_powers p (firstTrace p A) α β ha hm] at ht'
    linear_combination -ht'

/-- The formal zeta series of the genuine extension-field point counts is
the rational Hasse–Weil expression with its actual first trace. -/
theorem actualZeta_eq (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    actualZeta p A =
      (1 - X * C (firstTrace p A : ℂ) + X ^ 2 * C (p : ℂ)) *
        ((1 - X)⁻¹ * (1 - X * C (p : ℂ))⁻¹) := by
  obtain ⟨α, β, ha, hm⟩ := exist_two_roots (firstTrace p A : ℂ) (p : ℂ)
  unfold actualZeta
  rw [actualCounts_eq p hp hA α β ha hm, twoRootCounts_zeta,
    geometric_eq_inv (1 : ℂ), geometric_eq_inv (p : ℂ)]
  have hs : C α + C β = C (firstTrace p A : ℂ) := by rw [← map_add, ha]
  have hp' : C α * C β = C (p : ℂ) := by rw [← map_mul, hm]
  have hF : linearFactor α * linearFactor β =
      (1 - X * C (firstTrace p A : ℂ) + X ^ 2 * C (p : ℂ)) := by
    unfold linearFactor
    linear_combination -(X : Series) * hs + X ^ 2 * hp'
  rw [hF]
  simp [linearFactor]

end
end ManuscriptAudit.Paper5ActualHasseWeil

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5ActualHasseWeil.actualZeta_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
