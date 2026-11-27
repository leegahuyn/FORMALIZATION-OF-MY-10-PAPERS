import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticResidueClass
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticTwistCoefficientFormula
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts

/-! Six finite checks give the exact arithmetic trace for every twist of a certified split row. -/

namespace ManuscriptAudit.Paper5SplitTwistCertificate

open FiniteFieldPointCount CubicSplitExtensionTraceRecurrence
open CubicSexticTwistCoefficientFormula Paper5PrintedPointCounts
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

structure Certificate (p : ℕ) [Fact p.Prime] where
  k : ℕ
  z : ZMod p
  a : ℤ
  b : ℤ
  representative : Fin 6 → ℕ
  lower : 5 ≤ p
  card : p = 6 * k + 1
  primitive : IsPrimitiveRoot z 3
  norm : a ^ 2 - a * b + b ^ 2 = (p : ℤ)
  cover : ∀ A : ZMod p, A ≠ 0 → ∃ j : Fin 6, (representative j : ZMod p) ≠ 0 ∧
    A ^ k = (representative j : ZMod p) ^ k
  check : ∀ j : Fin 6,
    (p : ℤ) + 1 - (enumeratedPointsFor p (representative j) : ℤ) =
      predictedTrace z ((representative j : ZMod p) ^ k) a b

variable {p : ℕ} [Fact p.Prime]

/-- Reducing the centered printed cubic at its indexing prime kills its linear term. -/
theorem paper_curve_eq (A : ZMod p) :
    paper5TraceCurve p A = shortCubic (0 : ZMod p) A := by
  simp [paper5TraceCurve, shortCubic, ZMod.natCast_self]

theorem small_cast_ne_zero (n : ℕ) (hn : 0 < n) (h : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro he
  have hm := (ZMod.natCast_eq_natCast_iff' n 0 p).mp he
  rw [Nat.mod_eq_of_lt h, Nat.zero_mod] at hm
  omega

def prediction (c : Certificate p) (A : ZMod p) : ℤ :=
  predictedTrace c.z (A ^ c.k) c.a c.b

theorem prediction_eq_count (c : Certificate p) {A : ZMod p} (hA : A ≠ 0) :
    prediction c A = signedTrace A := by
  have hk : 0 < c.k := by have := c.lower; have := c.card; omega
  have h₂ : (2 : ZMod p) ≠ 0 := small_cast_ne_zero 2 (by decide) (by have := c.lower; omega)
  have h₃ : (3 : ZMod p) ≠ 0 := small_cast_ne_zero 3 (by decide) (by have := c.lower; omega)
  obtain ⟨j, hR, hPow⟩ := c.cover A hA
  have hCard : Fintype.card (ZMod p) = 6 * c.k + 1 := by rw [ZMod.card, c.card]
  have hEq := CubicSexticResidueClass.signedTrace_eq_of_residue hk hCard h₂ h₃ hA hR hPow
  have hc := projective_count_eq_enumeratedFor (p := p) (A := c.representative j) c.lower hR
  rw [paper_curve_eq] at hc
  have hCount : signedTrace (c.representative j : ZMod p) =
      prediction c (c.representative j : ZMod p) := by
    unfold signedTrace prediction
    rw [hc, ZMod.card]
    exact c.check j
  unfold prediction at ⊢
  rw [hPow]
  exact hCount.symm.trans hEq.symm

end
end ManuscriptAudit.Paper5SplitTwistCertificate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5SplitTwistCertificate.prediction_eq_count
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
