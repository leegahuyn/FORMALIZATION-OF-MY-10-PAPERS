import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitPrimeTateCoefficients
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitExtensionTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.CubicExtensionFrobeniusAt

/-! All finite-extension counts from exact native split-prime Tate Frobenius. -/

namespace ManuscriptAudit.CubicSplitPrimeTateExtensions

open Polynomial Module FiniteFieldPointCount CubicNonsplitThreeAdicTrace CubicThreeTorsionOrdinate
open CubicNonsplitFrobeniusTrace CubicExtensionFrobeniusAt CubicSplitExtensionTraceRecurrence
open CubicSplitPrimeTateCoefficients CubicFrobeniusTranscendentalRelation PowerTateModule
open Paper5NonsplitFrobeniusModFour
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (L D : Type*) [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L] [Field D] [Fintype D] [DecidableEq D] [Algebra (ZMod p) D]

/-- The actual Frobenius power has the signed extension count and determinant equal to the field size. -/
theorem power_trace_det (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let F := native p L A l ^ (Module.finrank (ZMod p) D)
    LinearMap.trace ℤ_[l] _ F = (signedTrace (algebraMap (ZMod p) D A) : ℤ_[l]) ∧
      LinearMap.det F = (Fintype.card D : ℤ_[l]) := by
  let n := Module.finrank (ZMod p) D
  let F := native p L A l
  obtain ⟨ht, hd⟩ := trace_det p L hp hs hA l hl
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have hdiv : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  have hAri := extension_trace_eq_recurrence (E := D) h₂ h₃ hA hdiv
  rw [ZMod.card] at hAri
  change signedTrace (algebraMap (ZMod p) D A) =
    Paper5PrintedRecurrence.recurrence p (arithmeticTrace (ZMod p) A) n at hAri
  have hTrace := Paper5LinearTraceRecurrence.trace_pow_eq_recurrence
    (basis p L hp hA l hl) F p (arithmeticTrace (ZMod p) A) ht hd n
  have hCard : Fintype.card D = p ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := D), ZMod.card]
  constructor
  · exact hTrace.trans (congrArg (fun z : ℤ => (z : ℤ_[l])) hAri.symm)
  · change LinearMap.det (F ^ n) = (Fintype.card D : ℤ_[l])
    rw [map_pow, hd, hCard, Nat.cast_pow]

variable [Algebra D L] [IsScalarTower (ZMod p) D L]

/-- The actual relative Frobenius endomorphism obtained using the extension field D. -/
def relative (A : ZMod p) (l : ℕ) [Fact l.Prime] :
    Module.End ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) :=
  endMap l (pointMapAt D L (Curve (algebraMap (ZMod p) D A)) (Curve (algebraMap (ZMod p) L A))
    ((centered_baseChange D L _).trans (congrArg Curve (IsScalarTower.algebraMap_apply (ZMod p) D L A).symm))
    (FiniteField.frobeniusAlgHom D L))

/-- The actual relative extension Frobenius agrees with the prime Frobenius power. -/
theorem relative_eq_power (A : ZMod p) (l : ℕ) [Fact l.Prime] :
    relative p L D A l = native p L A l ^ (Module.finrank (ZMod p) D) := by
  have hA : algebraMap D L (algebraMap (ZMod p) D A) = algebraMap (ZMod p) L A :=
    (IsScalarTower.algebraMap_apply (ZMod p) D L A).symm
  have hCard : Fintype.card D = Fintype.card (ZMod p) ^ (Module.finrank (ZMod p) D) :=
    Module.card_eq_pow_finrank (K := ZMod p) (V := D)
  have h := point_eq_pow (ZMod p) D L (Module.finrank (ZMod p) D) A hA hCard
  change endMap l _ = native p L A l ^ _
  rw [h, map_pow]
  rfl

/-- The exact full characteristic polynomial of the actual extension Frobenius. -/
theorem relative_charpoly (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let B := basis p L hp hA l hl
    letI : Module.Free ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := Module.Free.of_basis B
    letI : Module.Finite ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := Module.Finite.of_basis B
    (relative p L D A l).charpoly =
      X ^ 2 - C (signedTrace (algebraMap (ZMod p) D A) : ℤ_[l]) * X + C (Fintype.card D : ℤ_[l]) := by
  let B := basis p L hp hA l hl
  letI : Module.Free ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := Module.Free.of_basis B
  letI : Module.Finite ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A)) := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := power_trace_det p L D hp hs hA l hl
  dsimp only at ht hd ⊢
  rw [relative_eq_power, ← LinearMap.charpoly_toMatrix _ B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

end

end ManuscriptAudit.CubicSplitPrimeTateExtensions

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicSplitPrimeTateExtensions.power_trace_det,
      ``ManuscriptAudit.CubicSplitPrimeTateExtensions.relative_eq_power,
      ``ManuscriptAudit.CubicSplitPrimeTateExtensions.relative_charpoly] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
