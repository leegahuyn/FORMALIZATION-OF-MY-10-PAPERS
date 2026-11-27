import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinaryAllPrimeTate
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularAllFiniteFields
import PrimalitySheafVerification.ManuscriptAudit.CubicExtensionFrobeniusAt
import PrimalitySheafVerification.ManuscriptAudit.Paper5GoodPrimeTateEuler

/-! Native Tate coefficients and the integral local numerator for every centered
good finite-field cubic and every coefficient prime distinct from the characteristic. -/

namespace ManuscriptAudit.CubicAllGoodFiniteFieldTate

open Module Polynomial PowerTateModule
open CubicNonsplitThreeAdicTrace (GeometricPoints arithmeticPointFrobenius)
open CubicNonsplitFrobeniusTrace (pointMapAt centered_baseChange)
open CubicThreeTorsionOrdinate (Curve)
open CubicSplitExtensionTraceRecurrence (signedTrace)
open Paper5GoodPrimeTateEuler (localNumerator localNumerator_eval)
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E L : Type) [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod p) E] [CharP E p]
  [Field L] [DecidableEq L] [Algebra E L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

abbrev actual (A : E) : Module.End ℤ_[l] (Tate l (GeometricPoints E L A)) :=
  endMap l (arithmeticPointFrobenius E L A)

/-- The genuine geometric Tate module has an integral basis of rank two. -/
def basis (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints E L A)) := by
  have hmod := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  by_cases hn : p % 3 = 2
  · exact CubicSupersingularTatePointCount.tateBasis p L l E hp hn hl.symm hA
  · have hs : p % 3 = 1 := by omega
    exact CubicOrdinaryAllPrimeTateRank.basis p E L l hp hs hA hl

/-- The trace is the signed count on the genuine projective curve and the determinant is the field size. -/
theorem trace_det (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    LinearMap.trace ℤ_[l] _ (actual E L l A) = (signedTrace A : ℤ_[l]) ∧
      LinearMap.det (actual E L l A) = (Fintype.card E : ℤ_[l]) := by
  have hmod := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  by_cases hn : p % 3 = 2
  · have ht := CubicSupersingularAllFiniteFields.arithmetic_power_trace p l E E L hp hn hl.symm hA
    exact ⟨by
      simpa only [actual, signedTrace, finrank_self, pow_one, Algebra.algebraMap_self_apply] using ht,
      CubicSupersingularAllFiniteFields.arithmetic_determinant p l E L hp hn hl.symm hA⟩
  · have hs : p % 3 = 1 := by omega
    exact CubicOrdinaryAllPrimeTate.trace_det p E L l hp hs hA hl

/-- The characteristic polynomial is computed on the full native rank-two module. -/
theorem charpoly (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    let B := basis p E L l hp hA hl
    letI := Module.Free.of_basis B
    letI := Module.Finite.of_basis B
    (actual E L l A).charpoly =
      X ^ 2 - C (signedTrace A : ℤ_[l]) * X + C (Fintype.card E : ℤ_[l]) := by
  let B := basis p E L l hp hA hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det p E L l hp hA hl
  change (actual E L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix _ B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

theorem euler_numerator (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (hl : p ≠ l) (z : ℤ_[l]) :
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints E L A))) - z • actual E L l A) =
      (localNumerator (signedTrace A) (Fintype.card E)).eval₂ (Int.castRingHom ℤ_[l]) z := by
  obtain ⟨ht, hd⟩ := trace_det p E L l hp hA hl
  rw [RankTwoEulerDeterminant.linear_determinant (basis p E L l hp hA hl),
    localNumerator_eval, ht, hd] <;> ring

variable (D : Type) [Field D] [Fintype D] [DecidableEq D] [Algebra E D]
  [Algebra (ZMod p) D] [CharP D p] [IsScalarTower (ZMod p) E D]
  [Algebra D L] [IsScalarTower E D L]

/-- Each extension-degree power of the original native Frobenius gives the genuine count and determinant over the extension. -/
theorem power_trace_det (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (hl : p ≠ l) :
    let F := actual E L l A ^ finrank E D
    LinearMap.trace ℤ_[l] _ F = (signedTrace (algebraMap E D A) : ℤ_[l]) ∧
      LinearMap.det F = (Fintype.card D : ℤ_[l]) := by
  have hmod := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  obtain ⟨_, hd⟩ := trace_det p E L l hp hA hl
  constructor
  · by_cases hn : p % 3 = 2
    · simpa only [actual, signedTrace] using
        CubicSupersingularAllFiniteFields.arithmetic_power_trace p l E D L hp hn hl.symm hA
    · have hs : p % 3 = 1 := by omega
      exact CubicOrdinaryAllPrimeTate.extension_trace p E L l D hp hs hA hl
  · rw [map_pow, hd, Module.card_eq_pow_finrank (K := E) (V := D), Nat.cast_pow]


/-- The relative operator is the genuine Frobenius on the specified geometric model. -/
abbrev relative (A : E) : Module.End ℤ_[l] (Tate l (GeometricPoints E L A)) :=
  endMap l (pointMapAt D L (Curve (algebraMap E D A)) (Curve (algebraMap E L A))
    ((centered_baseChange D L _).trans (congrArg Curve (IsScalarTower.algebraMap_apply E D L A).symm))
    (FiniteField.frobeniusAlgHom D L))

theorem relative_eq_power (A : E) :
    relative E L l D A = actual E L l A ^ finrank E D := by
  have h := CubicExtensionFrobeniusAt.point_eq_pow E D L (finrank E D) A
    (IsScalarTower.algebraMap_apply E D L A).symm (Module.card_eq_pow_finrank (K := E) (V := D))
  change endMap l _ = endMap l _ ^ finrank E D
  rw [h, map_pow]

/-- The exact integral numerator on every relative native Tate module over a good finite base. -/
theorem relative_euler_numerator (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (hl : p ≠ l) (z : ℤ_[l]) :
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints E L A))) - z • relative E L l D A) =
      (localNumerator (signedTrace (algebraMap E D A)) (Fintype.card D)).eval₂
        (Int.castRingHom ℤ_[l]) z := by
  rw [relative_eq_power, RankTwoEulerDeterminant.linear_determinant (basis p E L l hp hA hl),
    localNumerator_eval]
  have h := power_trace_det p E L l D hp hA hl
  dsimp only at h
  rw [h.1, h.2] <;> ring

end
end ManuscriptAudit.CubicAllGoodFiniteFieldTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicAllGoodFiniteFieldTate.basis,
      ``ManuscriptAudit.CubicAllGoodFiniteFieldTate.trace_det,
      ``ManuscriptAudit.CubicAllGoodFiniteFieldTate.charpoly,
      ``ManuscriptAudit.CubicAllGoodFiniteFieldTate.euler_numerator,
      ``ManuscriptAudit.CubicAllGoodFiniteFieldTate.power_trace_det,
      ``ManuscriptAudit.CubicAllGoodFiniteFieldTate.relative_eq_power,
      ``ManuscriptAudit.CubicAllGoodFiniteFieldTate.relative_euler_numerator] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
