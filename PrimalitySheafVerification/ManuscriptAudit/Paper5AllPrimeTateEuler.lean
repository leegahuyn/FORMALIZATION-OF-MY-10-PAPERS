import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.Paper5GoodPrimeTateEuler
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitAllPrimeTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitAllPrimeAdic

/-! One integral Euler numerator describes the complex analytic expression and the
native arithmetic Frobenius determinant at every coefficient prime away from p. -/

namespace ManuscriptAudit.Paper5AllPrimeTateEuler

open Module Polynomial PowerTateModule Paper5ActualHasseWeil
open CubicNonsplitThreeAdicTrace CubicFrobeniusTranscendentalRelation
open Paper5GoodPrimeTateEuler Paper5GoodPrimeTate Paper5NonsplitFrobeniusModFour
open CubicSplitPrimeTateExtensions (relative relative_eq_power)
open Paper5ActualAnalyticLocalZeta (rationalZeta pointTerm actual_local_zeta)
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open scoped Padic

noncomputable section
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L]
  [DecidableEq L] [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

abbrev actual (A : ZMod p) : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) :=
  endMap l (arithmeticPointFrobenius (ZMod p) L A)

/-- The same geometric Tate group is free of rank two at every coefficient prime l≠p. -/
def actualBasis (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l) :
    Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := by
  have hmod := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  by_cases hn : p % 3 = 2
  · exact Paper5NonsplitAllPrimeAdic.actualBasis p L l hp hn hl.symm hA
  · have hs : p % 3 = 1 := by omega
    exact CubicSplitAllPrimeTateRank.nativeBasis (L := L) hp hs hA l hl

/-- Arithmetic trace and cardinality determinant for all good prime-field centered curves. -/
theorem base_coefficients (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l) :
    LinearMap.trace ℤ_[l] _ (actual p L l A) = (firstTrace p A : ℤ_[l]) ∧
      LinearMap.det (actual p L l A) = (p : ℤ_[l]) := by
  have hmod := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  by_cases hn : p % 3 = 2
  · have ht : firstTrace p A = 0 :=
      (CubicTraceClassification.paper5_trace_eq_zero_iff hp hA).mpr hn
    obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
    have hq : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hn
    exact ⟨by simpa only [ht, Int.cast_zero, actual] using
      actual_prime_adic_trace_zero (ZMod p) L l h₂ h₃ hA hq,
      Paper5NonsplitAllPrimeAdic.determinant p L l hp hn hl.symm hA⟩
  · have hs : p % 3 = 1 := by omega
    have h := CubicSplitAllPrimeTate.trace_det p L l hp hs hA hl
    have hcurve : FiniteFieldPointCount.shortCubic (0 : ZMod p) A = paper5TraceCurve p A := by
      ext <;> simp [FiniteFieldPointCount.shortCubic, paper5TraceCurve]
    simpa only [CubicSplitPrimeTateCoefficients.arithmeticTrace_eq, hcurve, firstTrace] using h

/-- The integral Euler numerator of the actual base Frobenius, at every coefficient prime. -/
theorem base_euler_numerator (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l)
    (z : ℤ_[l]) :
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))) -
      z • actual p L l A) =
      (localNumerator (firstTrace p A) p).eval₂ (Int.castRingHom ℤ_[l]) z := by
  obtain ⟨ht, hd⟩ := base_coefficients p L l hp hA hl
  rw [RankTwoEulerDeterminant.linear_determinant (actualBasis p L l hp hA hl),
    localNumerator_eval, ht, hd] <;> ring

/-- The same integral polynomial occurs in the native Tate determinant and in the
already identified complex local zeta expression. -/
theorem shared_analytic_numerator (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l)
    (z : ℤ_[l]) (w : ℂ) :
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))) -
      z • actual p L l A) =
      (localNumerator (firstTrace p A) p).eval₂ (Int.castRingHom ℤ_[l]) z ∧
    rationalZeta (p : ℂ) (firstTrace p A : ℂ) w =
      (localNumerator (firstTrace p A) p).eval₂ (Int.castRingHom ℂ) w /
        ((1 - w) * (1 - (p : ℂ) * w)) :=
  ⟨base_euler_numerator p L l hp hA hl z, analytic_local_uses_numerator p A w⟩

/-- Convergence of the actual point-count series and its complex local zeta use this same polynomial. -/
theorem actual_analytic_and_tate (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l)
    (z : ℤ_[l]) {w : ℂ} (hw : ‖w‖ < 1 / (p : ℝ)) :
    Summable (fun n : ℕ => ‖pointTerm p A w n‖) ∧
    Complex.exp (∑' n : ℕ, pointTerm p A w n) =
      (localNumerator (firstTrace p A) p).eval₂ (Int.castRingHom ℂ) w /
        ((1 - w) * (1 - (p : ℂ) * w)) ∧
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))) -
      z • actual p L l A) =
      (localNumerator (firstTrace p A) p).eval₂ (Int.castRingHom ℤ_[l]) z := by
  obtain ⟨hSum, hExp⟩ := actual_local_zeta p hp hA hw
  obtain ⟨hDet, hRat⟩ := shared_analytic_numerator p L l hp hA hl z w
  exact ⟨hSum, hExp.trans hRat, hDet⟩

variable (D : Type*) [Field D] [Fintype D] [DecidableEq D] [Algebra (ZMod p) D]

/-- The actual power for a finite extension has the signed count and size of that extension. -/
theorem extension_power_coefficients (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (hl : p ≠ l) :
    let F := actual p L l A ^ finrank (ZMod p) D
    LinearMap.trace ℤ_[l] _ F = (extensionTrace p D A : ℤ_[l]) ∧
      LinearMap.det F = (Fintype.card D : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := base_coefficients p L l hp hA hl
  have hRec : extensionTrace p D A =
      Paper5PrintedRecurrence.recurrence p (firstTrace p A) (finrank (ZMod p) D) :=
    Paper5PrintedActualExtensionCounts.actual_extension_trace_eq_recurrence (E := D) hp hA
  constructor
  · rw [hRec]
    exact Paper5LinearTraceRecurrence.trace_pow_eq_recurrence (actualBasis p L l hp hA hl)
      (actual p L l A) p (firstTrace p A) ht hd (finrank (ZMod p) D)
  · rw [map_pow, hd, Module.card_eq_pow_finrank (K := ZMod p) (V := D), ZMod.card, Nat.cast_pow]

variable [Algebra D L] [IsScalarTower (ZMod p) D L]

/-- The verified integral Euler numerator is also the determinant of the actual relative operator. -/
theorem native_relative_euler_numerator (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (hl : p ≠ l) (z : ℤ_[l]) :
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))) -
      z • relative p L D A l) =
      (localNumerator (extensionTrace p D A) (Fintype.card D)).eval₂
        (Int.castRingHom ℤ_[l]) z := by
  rw [RankTwoEulerDeterminant.linear_determinant (actualBasis p L l hp hA hl), localNumerator_eval]
  have h := extension_power_coefficients p L l D hp hA hl
  dsimp only at h
  rw [relative_eq_power]
  change 1 - z * LinearMap.trace ℤ_[l] _ (actual p L l A ^ finrank (ZMod p) D) +
    z ^ 2 * LinearMap.det (actual p L l A ^ finrank (ZMod p) D) = _
  rw [h.1, h.2] <;> ring

end

end ManuscriptAudit.Paper5AllPrimeTateEuler

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.Paper5AllPrimeTateEuler.actualBasis,
      ``ManuscriptAudit.Paper5AllPrimeTateEuler.base_coefficients,
      ``ManuscriptAudit.Paper5AllPrimeTateEuler.base_euler_numerator,
      ``ManuscriptAudit.Paper5AllPrimeTateEuler.shared_analytic_numerator,
      ``ManuscriptAudit.Paper5AllPrimeTateEuler.actual_analytic_and_tate,
      ``ManuscriptAudit.Paper5AllPrimeTateEuler.extension_power_coefficients,
      ``ManuscriptAudit.Paper5AllPrimeTateEuler.native_relative_euler_numerator] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
