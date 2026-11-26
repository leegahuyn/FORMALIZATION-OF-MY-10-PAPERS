import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspHasseWeilSeries
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectivePoints

/-! Exact formal Hasse–Weil factors for the split projective node and its smooth locus. -/

namespace ManuscriptAudit.NodalHasseWeilSeries

open PowerSeries NodalProjectivePoints

noncomputable section

private abbrev Series := ℚ⟦X⟧

def nodalCounts (p : ℕ) [Fact p.Prime] : Series :=
  PowerSeries.X * PowerSeries.mk fun n =>
    (Nat.card (projectivePoints (GaloisField p (n + 1))) : ℚ)

def smoothCounts (p : ℕ) [Fact p.Prime] : Series :=
  PowerSeries.X * PowerSeries.mk fun n =>
    (Nat.card (model (GaloisField p (n + 1))).toProjective.Point : ℚ)

theorem nodalCounts_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    nodalCounts p = CuspPointCountSeries.cuspSeries p := by
  unfold nodalCounts CuspPointCountSeries.cuspSeries
  apply congrArg (fun r : Series => (PowerSeries.X : Series) * r)
  apply PowerSeries.ext
  intro n
  rw [coeff_mk, coeff_mk, (prime_power_point_counts p (n + 1) n.succ_ne_zero hp₂).1,
    (CuspPointCounts.prime_power_point_counts p (n + 1) n.succ_ne_zero).1]

theorem smoothCounts_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    smoothCounts p = CuspPointCountSeries.punctureSeries p := by
  unfold smoothCounts CuspPointCountSeries.punctureSeries
  apply congrArg (fun r : Series => (PowerSeries.X : Series) * r)
  apply PowerSeries.ext
  intro n
  rw [coeff_mk, coeff_mk,
    (CuspPointCounts.prime_power_point_counts p (n + 1) n.succ_ne_zero).2]
  have h := (prime_power_point_counts p (n + 1) n.succ_ne_zero hp₂).2
  exact congrArg (fun k : ℕ => (k : ℚ)) (by omega)

def nodalZeta (p : ℕ) [Fact p.Prime] : Series :=
  CuspHasseWeilSeries.zetaOfCountSeries (nodalCounts p)

def smoothZeta (p : ℕ) [Fact p.Prime] : Series :=
  CuspHasseWeilSeries.zetaOfCountSeries (smoothCounts p)

theorem nodalZeta_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    nodalZeta p = (1 - (PowerSeries.X : Series) * PowerSeries.C (p : ℚ))⁻¹ := by
  unfold nodalZeta
  rw [nodalCounts_eq p hp₂]
  exact CuspHasseWeilSeries.cuspZeta_eq_inv p

theorem smoothZeta_eq (p : ℕ) [Fact p.Prime] (hp₂ : p ≠ 2) :
    smoothZeta p = (1 - (PowerSeries.X : Series)) *
      (1 - (PowerSeries.X : Series) * PowerSeries.C (p : ℚ))⁻¹ := by
  unfold smoothZeta
  rw [smoothCounts_eq p hp₂]
  exact CuspHasseWeilSeries.punctureZeta_eq_mul_inv p

end
end ManuscriptAudit.NodalHasseWeilSeries

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalHasseWeilSeries.nodalCounts_eq,
      ``ManuscriptAudit.NodalHasseWeilSeries.smoothCounts_eq,
      ``ManuscriptAudit.NodalHasseWeilSeries.nodalZeta_eq,
      ``ManuscriptAudit.NodalHasseWeilSeries.smoothZeta_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
