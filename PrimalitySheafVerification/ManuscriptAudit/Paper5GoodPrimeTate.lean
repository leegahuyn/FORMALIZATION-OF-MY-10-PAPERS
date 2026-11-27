import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitPrimeTateExtensions
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualHasseWeil
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius

/-! Native Tate characteristic polynomials at every good prime and in every finite extension. -/

namespace ManuscriptAudit.Paper5GoodPrimeTate

open Polynomial Module PowerTateModule
open CubicNonsplitThreeAdicTrace (GeometricPoints)
open CubicSplitPrimeTateCoefficients (basis native)
open CubicSplitPrimeTateExtensions (relative relative_eq_power)
open Paper5ActualHasseWeil (firstTrace)
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
    [IsAlgClosed L] [DecidableEq L]

theorem base_coefficients (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] _ (native p L A l) = (firstTrace p A : ℤ_[l]) ∧
      LinearMap.det (native p L A l) = (p : ℤ_[l]) := by
  have hmod := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  by_cases hn : p % 3 = 2
  · have hbase : firstTrace p A = 0 :=
      (CubicTraceClassification.paper5_trace_eq_zero_iff hp hA).mpr hn
    obtain ⟨h₂, h₃⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
    have hq₃ : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hn
    have hq₂ : Fintype.card (ZMod p) % 2 = 1 := by
      obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
      rw [ZMod.card]
      omega
    constructor
    · simpa only [hbase, Int.cast_zero, native] using
        CubicNonsplitFrobeniusTrace.actual_prime_adic_trace_zero (ZMod p) L l h₂ h₃ hA hq₃
    · simpa only [native, CubicNonsplitPrimeAdicFrobenius.Action, ZMod.card] using
        CubicNonsplitPrimeAdicFrobenius.determinant_eq_card (ZMod p) L l h₂ h₃ hA hq₃ hq₂
          (basis p L hp hA l hl)
  · have hs : p % 3 = 1 := by omega
    have ht := CubicSplitPrimeTateCoefficients.trace_det p L hp hs hA l hl
    have hcurve : FiniteFieldPointCount.shortCubic (0 : ZMod p) A = paper5TraceCurve p A := by
      ext <;> simp [FiniteFieldPointCount.shortCubic, paper5TraceCurve]
    simpa only [CubicSplitPrimeTateCoefficients.arithmeticTrace_eq, hcurve, firstTrace] using ht

variable (D : Type*) [Field D] [Fintype D] [DecidableEq D] [Algebra (ZMod p) D]

def extensionTrace (A : ZMod p) : ℤ :=
  (Fintype.card D : ℤ) + 1 - (Nat.card ((paper5TraceCurve p A).baseChange D).toProjective.Point : ℤ)

theorem extension_power_coefficients (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let F := native p L A l ^ Module.finrank (ZMod p) D
    LinearMap.trace ℤ_[l] _ F = (extensionTrace p D A : ℤ_[l]) ∧
      LinearMap.det F = (Fintype.card D : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := base_coefficients p L hp hA l hl
  let B := basis p L hp hA l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  have hrecur : extensionTrace p D A =
      Paper5PrintedRecurrence.recurrence p (firstTrace p A) (Module.finrank (ZMod p) D) :=
    Paper5PrintedActualExtensionCounts.actual_extension_trace_eq_recurrence (E := D) hp hA
  constructor
  · rw [hrecur]
    exact Paper5LinearTraceRecurrence.trace_pow_eq_recurrence B (native p L A l) p (firstTrace p A)
      ht hd (Module.finrank (ZMod p) D)
  · dsimp only
    rw [map_pow, hd, Module.card_eq_pow_finrank (K := ZMod p) (V := D), ZMod.card, Nat.cast_pow]

theorem extension_power_charpoly (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let B := basis p L hp hA l hl
    letI := Module.Free.of_basis B
    letI := Module.Finite.of_basis B
    (native p L A l ^ Module.finrank (ZMod p) D).charpoly =
      X^2 - C (extensionTrace p D A : ℤ_[l]) * X + C (Fintype.card D : ℤ_[l]) := by
  let B := basis p L hp hA l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let F := native p L A l ^ Module.finrank (ZMod p) D
  change F.charpoly = _
  have h := extension_power_coefficients p L D hp hA l hl
  dsimp only at h
  rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, h.1, h.2]

variable [Algebra D L] [IsScalarTower (ZMod p) D L]

theorem relative_charpoly (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let B := basis p L hp hA l hl
    letI := Module.Free.of_basis B
    letI := Module.Finite.of_basis B
    (relative p L D A l).charpoly =
      X^2 - C (extensionTrace p D A : ℤ_[l]) * X + C (Fintype.card D : ℤ_[l]) := by
  let B := basis p L hp hA l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  change (relative p L D A l).charpoly = _
  rw [relative_eq_power]
  exact extension_power_charpoly p L D hp hA l hl

end
end ManuscriptAudit.Paper5GoodPrimeTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5GoodPrimeTate.base_coefficients,
      ``ManuscriptAudit.Paper5GoodPrimeTate.extension_power_coefficients,
      ``ManuscriptAudit.Paper5GoodPrimeTate.extension_power_charpoly,
      ``ManuscriptAudit.Paper5GoodPrimeTate.relative_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
