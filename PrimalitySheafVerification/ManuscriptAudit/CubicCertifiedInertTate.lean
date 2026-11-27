import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitPrimeFixedCounts
import PrimalitySheafVerification.ManuscriptAudit.EisensteinInertTorsionGrowth
import PrimalitySheafVerification.ManuscriptAudit.InertRotationTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTatePointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitAllPrimeAdic

/-! Exact Tate coefficients at every inert prime once the integral Frobenius identity is certified. -/

namespace ManuscriptAudit.CubicCertifiedInertTate

open Polynomial Module FiniteFieldPointCount CubicThreeTorsionOrdinate
open PowerTorsionTower PowerTateModule PrimeDivisibilityFromTorsionTower
open WeierstrassAlgebraicPointFiniteOrder CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace
open CubicSplitExtensionTraceRecurrence RotationNormUnit
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L]

/-- The data are a literal native endomorphism identity and its integral arithmetic coefficients. -/
structure IntegralReference where
  goodPrime : 5 ≤ p
  splitPrime : p % 3 = 1
  A : ZMod p
  nonzeroA : A ≠ 0
  rotation : AddMonoid.End (GeometricPoints (ZMod p) L A)
  quadratic : rotation ^ 2 + rotation + 1 = 0
  a : ℤ
  b : ℤ
  native : arithmeticPointFrobenius (ZMod p) L A = combination rotation a b
  trace : signedTrace A = 2 * a - b
  norm : a ^ 2 - a * b + b ^ 2 = (p : ℤ)

variable {p L} (c : IntegralReference p L) (l : ℕ) [Fact l.Prime]

abbrev Points := GeometricPoints (ZMod p) L c.A

abbrev action : Module.End ℤ_[l] (Tate l (Points c)) :=
  endMap l (arithmeticPointFrobenius (ZMod p) L c.A)

/-- All true geometric torsion levels have rank two at each inert coefficient prime. -/
theorem card_and_transition (hl : l % 3 = 2) :
    (∀ n, Nat.card (PowerTorsion l (Points c) n) = (l ^ 2) ^ n) ∧
      ∀ n, Function.Surjective (transition l (Points c) n) := by
  have hlp : p ≠ l := by
    intro he
    have hs := c.splitPrime
    rw [he, hl] at hs
    contradiction
  have hc := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : l.Prime)).mpr hlp
  obtain ⟨h₂, h₃⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) c.goodPrime
  apply EisensteinInertTorsionGrowth.card_and_transition l p hl (Fact.out : p.Prime).one_lt
    hc c.rotation (arithmeticPointFrobenius (ZMod p) L c.A) c.quadratic c.a c.b c.native c.norm
  intro n hn
  simpa only [c.trace] using
    CubicSplitPrimeFixedCounts.finite_and_card p L h₂ h₃ c.splitPrime c.nonzeroA n hn

def firstBasis (hl : l % 3 = 2) :
    Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l (Points c) 1) :=
  FirstPrimeTorsionBasis.basis l (Points c) (by
    simpa only [pow_one] using (card_and_transition c l hl).1 1)

variable [hAlg : Algebra.IsAlgebraic (ZMod p) L]

include hAlg in
theorem scalar_surjective (hl : l % 3 = 2) :
    Function.Surjective (fun P : Points c => l • P) := by
  apply surjective_nsmul_of_surjective_transitions l (Points c) _ (card_and_transition c l hl).2
  intro P
  let e := CubicSplitPrimeFixedCounts.transport (centered_baseChange (ZMod p) L c.A)
  obtain ⟨Q, rfl⟩ := e.surjective P
  obtain ⟨m, hm, hQ⟩ := exists_positive_nsmul_eq_zero (ZMod p) L (Curve c.A) Q
  exact ⟨m, hm, by rw [← map_nsmul e, hQ, map_zero]⟩

def basis (hl : l % 3 = 2) : Basis (Fin 2) ℤ_[l] (Tate l (Points c)) :=
  InertRotationTate.basis l (Points c) (firstBasis c l hl) (scalar_surjective c l hl)

include hAlg in
theorem trace_det (hl : l % 3 = 2) :
    LinearMap.trace ℤ_[l] (Tate l (Points c)) (action c l) = (signedTrace c.A : ℤ_[l]) ∧
      LinearMap.det (action c l) = (p : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := InertRotationTate.trace_det l (Points c) (firstBasis c l hl)
    (scalar_surjective c l hl) hl c.rotation (arithmeticPointFrobenius (ZMod p) L c.A)
    c.quadratic c.a c.b c.native
  rw [← c.trace] at ht
  rw [c.norm, Int.cast_natCast] at hd
  exact ⟨ht, hd⟩

include hAlg in
theorem charpoly (hl : l % 3 = 2) :
    letI := Module.Free.of_basis (basis c l hl)
    letI := Module.Finite.of_basis (basis c l hl)
    (action c l).charpoly = X ^ 2 - C (signedTrace c.A : ℤ_[l]) * X + C (p : ℤ_[l]) := by
  let B := basis c l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det c l hl
  change (action c l).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action c l) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

include hAlg in
theorem trace_eq_extension_count (E : Type*) [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] (hl : l % 3 = 2) :
    LinearMap.trace ℤ_[l] (Tate l (Points c)) ((action c l) ^ Module.finrank (ZMod p) E) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve p c.A).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det c l hl
  have hW : paper5TraceCurve p c.A = shortCubic (0 : ZMod p) c.A := by
    simp [paper5TraceCurve, shortCubic]
  exact Paper5SplitTatePointCounts.trace_power_eq_extension_count (p := p) (E := E)
    c.goodPrime c.splitPrime c.nonzeroA (basis c l hl) (action c l)
    (by simpa only [signedTrace, ZMod.card, hW] using ht) hd

end
end ManuscriptAudit.CubicCertifiedInertTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCertifiedInertTate.card_and_transition,
      ``ManuscriptAudit.CubicCertifiedInertTate.trace_det,
      ``ManuscriptAudit.CubicCertifiedInertTate.charpoly,
      ``ManuscriptAudit.CubicCertifiedInertTate.trace_eq_extension_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
