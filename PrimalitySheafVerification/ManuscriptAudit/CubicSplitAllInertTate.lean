import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitIntegralFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CubicCertifiedInertTate
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusSigns

/-! Actual Tate rank and Frobenius coefficients for every split base prime and inert coefficient prime. -/

namespace ManuscriptAudit.CubicSplitAllInertTate

open Polynomial CubicCertifiedInertTate CubicSplitExtensionTraceRecurrence
open CubicNonsplitThreeAdicTrace CubicFrobeniusTranscendentalRelation
open CubicNaturalCMOperations CubicSplitIntegralFrobenius CubicThreeFrobeniusSigns
open Paper5NonsplitFrobeniusModFour PowerTateModule PowerTorsionTower
open scoped Padic

noncomputable section
open scoped Classical

variable (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra (ZMod p) L]
  [DecidableEq L] [IsAlgClosed L]

/-- Every nonzero twist at a good split prime supplies the native certificate required
by the inert-prime torsion proof. -/
def reference (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) :
    IntegralReference p L := by
  have hsmall := small_char p (ZMod p) hp
  let h₂ := hsmall.1
  let h₃ := hsmall.2
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ringChar.eq (ZMod p) p]; omega
  have hCard : Fintype.card (ZMod p) % 3 = 1 := by rw [ZMod.card]; exact hs
  have hd : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  let z := Classical.choose (finite_exists_primitive_cube_root hCard)
  have hz : IsPrimitiveRoot z 3 := Classical.choose_spec (finite_exists_primitive_cube_root hCard)
  have hz₁ : z ≠ 1 := hz.ne_one (by decide)
  let R := (rotation h₂ h₃ hA hz.pow_eq_one).atField L
  let c := exists_integral_combination (L := L) h₂ h₃ hc hd hA hz.pow_eq_one hz₁
  let a := Classical.choose c
  let ca := Classical.choose_spec c
  let b := Classical.choose ca
  have hab := Classical.choose_spec ca
  have hNorm : a ^ 2 - a * b + b ^ 2 = (p : ℤ) := by
    simpa only [ZMod.card] using hab.2.1
  exact ⟨hp, hs, A, hA, R, rotation_quadratic h₂ h₃ hA hz.pow_eq_one L hz₁,
    a, b, hab.2.2, hab.1, hNorm⟩

@[simp] theorem reference_A (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) :
    (reference p L hp hs hA).A = A := rfl

variable [Algebra.IsAlgebraic (ZMod p) L]

/-- The native Frobenius has the arithmetic trace and determinant for every inert coefficient prime. -/
theorem trace_det (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l % 3 = 2) :
    let c := reference p L hp hs hA
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))
        (endMap l (arithmeticPointFrobenius (ZMod p) L A)) = (signedTrace A : ℤ_[l]) ∧
      LinearMap.det (action c l) = (p : ℤ_[l]) := by
  exact CubicCertifiedInertTate.trace_det (reference p L hp hs hA) l hl

/-- The actual characteristic polynomial for every inert coefficient prime. -/
theorem charpoly (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l % 3 = 2) :
    let c := reference p L hp hs hA
    letI := Module.Free.of_basis (basis c l hl)
    letI := Module.Finite.of_basis (basis c l hl)
    (action c l).charpoly = X ^ 2 - C (signedTrace A : ℤ_[l]) * X + C (p : ℤ_[l]) :=
  CubicCertifiedInertTate.charpoly (reference p L hp hs hA) l hl

end

end ManuscriptAudit.CubicSplitAllInertTate

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicSplitAllInertTate.reference,
      ``ManuscriptAudit.CubicSplitAllInertTate.reference_A,
      ``ManuscriptAudit.CubicSplitAllInertTate.trace_det,
      ``ManuscriptAudit.CubicSplitAllInertTate.charpoly] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
